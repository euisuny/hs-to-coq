Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Vst.MonadExports
     Vst.Representation Swap_ImplModel.

Import SockAPIPred.
Import TracePred.

Definition select_loop_spec :=
  DECLARE _select_loop
  WITH k : itree socketE unit,
       st : SocketMap,
       server_addr : endpoint_id,
       server_fd : sockfd,
       initial_msg : string,
       msg_store_ptr : val,
       msg_store_sh : share
  PRE [ _server_socket OF tint, 
        _last_msg_store OF tptr (Tstruct _store noattr) ]
  PROP ( consistent_world st;
         lookup_socket st server_fd = ListeningSocket server_addr ;
         0 <= descriptor server_fd < FD_SETSIZE ;
         writable_share msg_store_sh
       )
  LOCAL ( temp _server_socket (Vint (Int.repr (descriptor server_fd))) ;
          temp _last_msg_store msg_store_ptr 
        )
  SEP ( SOCKAPI st ;
        ITREE ( select_loop real_swap_app server_addr ([], initial_msg);; k ) ;
        field_at msg_store_sh (Tstruct _store noattr) [] (rep_store initial_msg)
                 msg_store_ptr  
      )
  POST [ tint ]
    PROP ( False )
    LOCAL ( temp ret_temp (Vint (Int.repr 0)) )
    SEP ( ).  
