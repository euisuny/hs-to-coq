module Main where

-- Example Hello World server from https://wiki.haskell.org/Implement_a_chat_server

import Network.Socket

main :: IO ()
main = do
  sock <- socket AF_INET Stream 0    -- create new Socket on server
  setSocketOption sock ReuseAddr 1   -- make socket immediately reusable - eases debugging.
  bind sock (SockAddrInet 4242 iNADDR_ANY)   -- listen on TCP port 4242.
  listen sock 2                              -- set a max of 2 queued connections
  mainLoop sock                              -- unimplemented

mainLoop :: Socket -> IO ()
mainLoop sock = do
  -- `accept` returns a (conn, addr)
  -- where `conn` is the new socket object, usable to send and receive the data.
  -- `addr` is the address of the socket on the other end of the connection.
  --
  -- In order to accept the connection and handle it, the socket must be
  -- 1. Bound to an address
  -- 2. Listening for a connection
  conn <- accept sock     -- accept a connection and handle it
  runConn conn            -- run our server's logic
  mainLoop sock           -- repeat

runConn :: (Socket, SockAddr) -> IO ()
runConn (sock, _) = do
  -- Send data to socket. Socket must be connected to a remote socket. returns
  -- number of bytes sent. Apps are responsible for ensuring all data has been sent.
  send sock "Hello World!\n"
  -- `close` does not throw exceptions
  close sock
