{-# LINE 1 "Cbits.hsc" #-}
module Network.Socket.Cbits where



import Network.Socket.Imports

-- | This is the value of SOMAXCONN, typically 128.
-- 128 is good enough for normal network servers but
-- is too small for high performance servers.
maxListenQueue :: Int
maxListenQueue = 128
{-# LINE 12 "Cbits.hsc" #-}


{-# LINE 17 "Cbits.hsc" #-}
fGetFd :: CInt
fGetFd = 1
{-# LINE 19 "Cbits.hsc" #-}
fGetFl :: CInt
fGetFl = 3
{-# LINE 21 "Cbits.hsc" #-}
fdCloexec :: CInt
fdCloexec = 1
{-# LINE 23 "Cbits.hsc" #-}
oNonBlock :: CInt
oNonBlock = 4
{-# LINE 25 "Cbits.hsc" #-}

{-# LINE 31 "Cbits.hsc" #-}

{-# LINE 32 "Cbits.hsc" #-}
