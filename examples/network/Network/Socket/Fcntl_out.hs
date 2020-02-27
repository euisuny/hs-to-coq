{-# LINE 1 "Fcntl.hs" #-}
{-# LANGUAGE CPP #-}

module Network.Socket.Fcntl where

import qualified System.Posix.Internals


{-# LINE 8 "Fcntl.hs" #-}
import Network.Socket.Cbits

{-# LINE 10 "Fcntl.hs" #-}
import Network.Socket.Imports

-- | Set the nonblocking flag on Unix.
--   On Windows, nothing is done.
setNonBlockIfNeeded :: CInt -> IO ()
setNonBlockIfNeeded fd =
    System.Posix.Internals.setNonBlockingFD fd True

-- | Set the close_on_exec flag on Unix.
--   On Windows, nothing is done.
--
--   Since 2.7.0.0.
setCloseOnExecIfNeeded :: CInt -> IO ()

{-# LINE 26 "Fcntl.hs" #-}
setCloseOnExecIfNeeded fd = System.Posix.Internals.setCloseOnExec fd

{-# LINE 28 "Fcntl.hs" #-}


{-# LINE 30 "Fcntl.hs" #-}
foreign import ccall unsafe "fcntl"
  c_fcntl_read  :: CInt -> CInt -> CInt -> IO CInt

{-# LINE 33 "Fcntl.hs" #-}

-- | Get the close_on_exec flag.
--   On Windows, this function always returns 'False'.
--
--   Since 2.7.0.0.
getCloseOnExec :: CInt -> IO Bool

{-# LINE 42 "Fcntl.hs" #-}
getCloseOnExec fd = do
    flags <- c_fcntl_read fd fGetFd 0
    let ret = flags .&. fdCloexec
    return (ret /= 0)

{-# LINE 47 "Fcntl.hs" #-}

-- | Get the nonblocking flag.
--   On Windows, this function always returns 'False'.
--
--   Since 2.7.0.0.
getNonBlock :: CInt -> IO Bool

{-# LINE 56 "Fcntl.hs" #-}
getNonBlock fd = do
    flags <- c_fcntl_read fd fGetFl 0
    let ret = flags .&. oNonBlock
    return (ret /= 0)

{-# LINE 61 "Fcntl.hs" #-}
