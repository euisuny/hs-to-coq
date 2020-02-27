#include "/Library/Frameworks/GHC.framework/Versions/8.6.3-x86_64/usr/lib/ghc-8.6.3/template-hsc.h"
#line 3 "Cbits.hsc"
#include "HsNet.h"
#line 13 "Cbits.hsc"
#if defined(mingw32_HOST_OS)
#line 16 "Cbits.hsc"
#else 
#line 25 "Cbits.hsc"
#if defined(HAVE_ADVANCED_SOCKET_FLAGS)
#line 30 "Cbits.hsc"
#endif 
#line 31 "Cbits.hsc"
#endif 

int main (void)
{
#line 13 "Cbits.hsc"
#if defined(mingw32_HOST_OS)
#line 16 "Cbits.hsc"
#else 
#line 25 "Cbits.hsc"
#if defined(HAVE_ADVANCED_SOCKET_FLAGS)
#line 30 "Cbits.hsc"
#endif 
#line 31 "Cbits.hsc"
#endif 
    hsc_line (1, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
    hsc_fputs ("module Network.Socket.Cbits where\n"
           "", hsc_stdout());
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_fputs ("\n"
           "import Network.Socket.Imports\n"
           "\n"
           "-- | This is the value of SOMAXCONN, typically 128.\n"
           "-- 128 is good enough for normal network servers but\n"
           "-- is too small for high performance servers.\n"
           "maxListenQueue :: Int\n"
           "maxListenQueue = ", hsc_stdout());
#line 11 "Cbits.hsc"
    hsc_const (SOMAXCONN);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (12, "Cbits.hsc");
    hsc_fputs ("\n"
           "", hsc_stdout());
#line 13 "Cbits.hsc"
#if defined(mingw32_HOST_OS)
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (14, "Cbits.hsc");
    hsc_fputs ("wsaNotInitialized :: CInt\n"
           "wsaNotInitialized = ", hsc_stdout());
#line 15 "Cbits.hsc"
    hsc_const (WSANOTINITIALISED);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (16, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
#line 16 "Cbits.hsc"
#else 
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (17, "Cbits.hsc");
    hsc_fputs ("fGetFd :: CInt\n"
           "fGetFd = ", hsc_stdout());
#line 18 "Cbits.hsc"
    hsc_const (F_GETFD);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (19, "Cbits.hsc");
    hsc_fputs ("fGetFl :: CInt\n"
           "fGetFl = ", hsc_stdout());
#line 20 "Cbits.hsc"
    hsc_const (F_GETFL);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (21, "Cbits.hsc");
    hsc_fputs ("fdCloexec :: CInt\n"
           "fdCloexec = ", hsc_stdout());
#line 22 "Cbits.hsc"
    hsc_const (FD_CLOEXEC);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (23, "Cbits.hsc");
    hsc_fputs ("oNonBlock :: CInt\n"
           "oNonBlock = ", hsc_stdout());
#line 24 "Cbits.hsc"
    hsc_const (O_NONBLOCK);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (25, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
#line 25 "Cbits.hsc"
#if defined(HAVE_ADVANCED_SOCKET_FLAGS)
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (26, "Cbits.hsc");
    hsc_fputs ("sockNonBlock :: CInt\n"
           "sockNonBlock = ", hsc_stdout());
#line 27 "Cbits.hsc"
    hsc_const (SOCK_NONBLOCK);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (28, "Cbits.hsc");
    hsc_fputs ("sockCloexec :: CInt\n"
           "sockCloexec = ", hsc_stdout());
#line 29 "Cbits.hsc"
    hsc_const (SOCK_CLOEXEC);
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (30, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
#line 30 "Cbits.hsc"
#endif 
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (31, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
#line 31 "Cbits.hsc"
#endif 
    hsc_fputs ("\n"
           "", hsc_stdout());
    hsc_line (32, "Cbits.hsc");
    hsc_fputs ("", hsc_stdout());
    return 0;
}
