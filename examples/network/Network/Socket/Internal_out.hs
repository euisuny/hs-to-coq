{-# LINE 1 "Internal.hs" #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}



-----------------------------------------------------------------------------
-- |
-- Module      :  Network.Socket.Internal
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/network/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- A module containing semi-public 'Network.Socket' internals.
-- Modules which extend the 'Network.Socket' module will need to use
-- this module while ideally most users will be able to make do with
-- the public interface.
--
-----------------------------------------------------------------------------

module Network.Socket.Internal
    (
    -- * Socket error functions
      throwSocketError
    , throwSocketErrorCode

{-# LINE 31 "Internal.hs" #-}

    -- * Guards for socket operations that may fail
    , throwSocketErrorIfMinus1_
    , throwSocketErrorIfMinus1Retry
    , throwSocketErrorIfMinus1Retry_
    , throwSocketErrorIfMinus1RetryMayBlock

    -- ** Guards that wait and retry if the operation would block
    -- | These guards are based on 'throwSocketErrorIfMinus1RetryMayBlock'.
    -- They wait for socket readiness if the action fails with @EWOULDBLOCK@
    -- or similar.
    , throwSocketErrorWaitRead
    , throwSocketErrorWaitWrite

    -- * Initialization
    , withSocketsDo

    -- * Low-level helpers
    , zeroMemory
    ) where

import GHC.Conc (threadWaitRead, threadWaitWrite)


{-# LINE 64 "Internal.hs" #-}
import Foreign.C.Error (throwErrno, throwErrnoIfMinus1Retry,
                        throwErrnoIfMinus1RetryMayBlock, throwErrnoIfMinus1_,
                        Errno(..), errnoToIOError)

{-# LINE 68 "Internal.hs" #-}


{-# LINE 72 "Internal.hs" #-}
import Network.Socket.Imports
import Network.Socket.Types

-- ---------------------------------------------------------------------
-- Guards for socket operations that may fail

-- | Throw an 'IOError' corresponding to the current socket error.
throwSocketError :: String  -- ^ textual description of the error location
                 -> IO a

-- | Like 'throwSocketError', but the error code is supplied as an argument.
--
-- On Windows, do not use errno.  Use a system error code instead.
throwSocketErrorCode :: String -> CInt -> IO a

-- | Throw an 'IOError' corresponding to the current socket error if
-- the IO action returns a result of @-1@.  Discards the result of the
-- IO action after error handling.
throwSocketErrorIfMinus1_
    :: (Eq a, Num a)
    => String  -- ^ textual description of the location
    -> IO a    -- ^ the 'IO' operation to be executed
    -> IO ()

{-# SPECIALIZE throwSocketErrorIfMinus1_ :: String -> IO CInt -> IO () #-}

-- | Throw an 'IOError' corresponding to the current socket error if
-- the IO action returns a result of @-1@, but retries in case of an
-- interrupted operation.
throwSocketErrorIfMinus1Retry
    :: (Eq a, Num a)
    => String  -- ^ textual description of the location
    -> IO a    -- ^ the 'IO' operation to be executed
    -> IO a

{-# SPECIALIZE throwSocketErrorIfMinus1Retry :: String -> IO CInt -> IO CInt #-}

-- | Throw an 'IOError' corresponding to the current socket error if
-- the IO action returns a result of @-1@, but retries in case of an
-- interrupted operation. Discards the result of the IO action after
-- error handling.
throwSocketErrorIfMinus1Retry_
    :: (Eq a, Num a)
    => String  -- ^ textual description of the location
    -> IO a    -- ^ the 'IO' operation to be executed
    -> IO ()
throwSocketErrorIfMinus1Retry_ loc m =
    void $ throwSocketErrorIfMinus1Retry loc m
{-# SPECIALIZE throwSocketErrorIfMinus1Retry_ :: String -> IO CInt -> IO () #-}

-- | Throw an 'IOError' corresponding to the current socket error if
-- the IO action returns a result of @-1@, but retries in case of an
-- interrupted operation.  Checks for operations that would block and
-- executes an alternative action before retrying in that case.
throwSocketErrorIfMinus1RetryMayBlock
    :: (Eq a, Num a)
    => String  -- ^ textual description of the location
    -> IO b    -- ^ action to execute before retrying if an
               --   immediate retry would block
    -> IO a    -- ^ the 'IO' operation to be executed
    -> IO a

{-# SPECIALIZE throwSocketErrorIfMinus1RetryMayBlock
        :: String -> IO b -> IO CInt -> IO CInt #-}


{-# LINE 176 "Internal.hs" #-}

throwSocketErrorIfMinus1RetryMayBlock name on_block act =
    throwErrnoIfMinus1RetryMayBlock name act on_block

throwSocketErrorIfMinus1Retry = throwErrnoIfMinus1Retry

throwSocketErrorIfMinus1_ = throwErrnoIfMinus1_

throwSocketError = throwErrno

throwSocketErrorCode loc errno =
    ioError (errnoToIOError loc (Errno errno) Nothing Nothing)


{-# LINE 190 "Internal.hs" #-}

-- | Like 'throwSocketErrorIfMinus1Retry', but if the action fails with
-- @EWOULDBLOCK@ or similar, wait for the socket to be read-ready,
-- and try again.
throwSocketErrorWaitRead :: (Eq a, Num a) => Socket -> String -> IO a -> IO a
throwSocketErrorWaitRead s name io = withFdSocket s $ \fd ->
    throwSocketErrorIfMinus1RetryMayBlock name
      (threadWaitRead $ fromIntegral fd) io

-- | Like 'throwSocketErrorIfMinus1Retry', but if the action fails with
-- @EWOULDBLOCK@ or similar, wait for the socket to be write-ready,
-- and try again.
throwSocketErrorWaitWrite :: (Eq a, Num a) => Socket -> String -> IO a -> IO a
throwSocketErrorWaitWrite s name io = withFdSocket s $ \fd ->
    throwSocketErrorIfMinus1RetryMayBlock name
      (threadWaitWrite $ fromIntegral fd) io

-- ---------------------------------------------------------------------------
-- WinSock support

{-| With older versions of the @network@ library (version 2.6.0.2 or earlier)
on Windows operating systems,
the networking subsystem must be initialised using 'withSocketsDo' before
any networking operations can be used. eg.

> main = withSocketsDo $ do {...}

It is fine to nest calls to 'withSocketsDo', and to perform networking operations
after 'withSocketsDo' has returned.

'withSocketsDo' is not necessary for the current network library.
However, for compatibility with older versions on Windows, it is good practice
to always call 'withSocketsDo' (it's very cheap).
-}
{-# INLINE withSocketsDo #-}
withSocketsDo :: IO a -> IO a

{-# LINE 241 "Internal.hs" #-}

withSocketsDo x = x


{-# LINE 245 "Internal.hs" #-}
