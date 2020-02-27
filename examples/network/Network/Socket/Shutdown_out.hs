{-# LINE 1 "Shutdown.hs" #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}



module Network.Socket.Shutdown (
    ShutdownCmd(..)
  , shutdown
  , gracefulClose
  ) where

import qualified Control.Exception as E
import Foreign.Marshal.Alloc (mallocBytes, free)

import Control.Concurrent (threadDelay)

{-# LINE 17 "Shutdown.hs" #-}
import Control.Concurrent (putMVar, takeMVar, newEmptyMVar)
import qualified GHC.Event as Ev
import System.Posix.Types (Fd(..))

{-# LINE 21 "Shutdown.hs" #-}

import Network.Socket.Buffer
import Network.Socket.Imports
import Network.Socket.Internal
import Network.Socket.Types

data ShutdownCmd = ShutdownReceive
                 | ShutdownSend
                 | ShutdownBoth
                 deriving Typeable

sdownCmdToInt :: ShutdownCmd -> CInt
sdownCmdToInt ShutdownReceive = 0
sdownCmdToInt ShutdownSend    = 1
sdownCmdToInt ShutdownBoth    = 2

-- | Shut down one or both halves of the connection, depending on the
-- second argument to the function.  If the second argument is
-- 'ShutdownReceive', further receives are disallowed.  If it is
-- 'ShutdownSend', further sends are disallowed.  If it is
-- 'ShutdownBoth', further sends and receives are disallowed.
shutdown :: Socket -> ShutdownCmd -> IO ()
shutdown s stype = void $ withFdSocket s $ \fd ->
  throwSocketErrorIfMinus1Retry_ "Network.Socket.shutdown" $
    c_shutdown fd $ sdownCmdToInt stype

foreign import CALLCONV unsafe "shutdown"
  c_shutdown :: CInt -> CInt -> IO CInt


{-# LINE 51 "Shutdown.hs" #-}
data Wait = MoreData | TimeoutTripped

{-# LINE 53 "Shutdown.hs" #-}

-- | Closing a socket gracefully.
--   This sends TCP FIN and check if TCP FIN is received from the peer.
--   The second argument is time out to receive TCP FIN in millisecond.
--   In both normal cases and error cases, socket is deallocated finally.
--
--   Since: 3.1.1.0
gracefulClose :: Socket -> Int -> IO ()
gracefulClose s tmout = sendRecvFIN `E.finally` close s
  where
    sendRecvFIN = do
        -- Sending TCP FIN.
        shutdown s ShutdownSend
        -- Waiting TCP FIN.

{-# LINE 70 "Shutdown.hs" #-}
        mevmgr <- Ev.getSystemEventManager
        case mevmgr of
          Nothing    -> recvEOFloop     -- non-threaded RTS
          Just evmgr -> recvEOFev evmgr

{-# LINE 75 "Shutdown.hs" #-}
    -- milliseconds. Taken from BSD fast clock value.
    clock = 200
    recvEOFloop = E.bracket (mallocBytes bufSize) free $ loop 0
      where
        loop delay buf = do
            -- We don't check the (positive) length.
            -- In normal case, it's 0. That is, only FIN is received.
            -- In error cases, data is available. But there is no
            -- application which can read it. So, let's stop receiving
            -- to prevent attacks.
            r <- recvBufNoWait s buf bufSize
            let delay' = delay + clock
            when (r == -1 && delay' < tmout) $ do
                threadDelay (clock * 1000)
                loop delay' buf

{-# LINE 91 "Shutdown.hs" #-}
    recvEOFev evmgr = do
        tmmgr <- Ev.getSystemTimerManager
        mvar <- newEmptyMVar
        E.bracket (register evmgr tmmgr mvar) (unregister evmgr tmmgr) $ \_ -> do
            wait <- takeMVar mvar
            case wait of
              TimeoutTripped -> return ()
              -- We don't check the (positive) length.
              -- In normal case, it's 0. That is, only FIN is received.
              -- In error cases, data is available. But there is no
              -- application which can read it. So, let's stop receiving
              -- to prevent attacks.
              MoreData       -> E.bracket (mallocBytes bufSize)
                                          free
                                          (\buf -> void $ recvBufNoWait s buf bufSize)
    register evmgr tmmgr mvar = do
        -- millisecond to microsecond
        key1 <- Ev.registerTimeout tmmgr (tmout * 1000) $
            putMVar mvar TimeoutTripped
        key2 <- withFdSocket s $ \fd' -> do
            let callback _ _ = putMVar mvar MoreData
                fd = Fd fd'

{-# LINE 114 "Shutdown.hs" #-}
            Ev.registerFd evmgr callback fd Ev.evtRead

{-# LINE 118 "Shutdown.hs" #-}
        return (key1, key2)
    unregister evmgr tmmgr (key1,key2) = do
        Ev.unregisterTimeout tmmgr key1
        Ev.unregisterFd evmgr key2

{-# LINE 123 "Shutdown.hs" #-}
    -- Don't use 4092 here. The GHC runtime takes the global lock
    -- if the length is over 3276 bytes in 32bit or 3272 bytes in 64bit.
    bufSize = 1024
