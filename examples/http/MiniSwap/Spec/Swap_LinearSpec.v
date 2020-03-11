(** * Linear specification of a swap server *)

(* The effect type [specE] used by the specification is defined
   in [Lib.LinearSpec_Interface] as

       Definition specE := failureE +' nondetE +' observerE.

   where [observerE] is defined there, [failureE] and [nondetE]
   are general-purpose exception and nondeterminism effects from
   [Free.Monad.Common].
 *)

Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

From Coq Require Import
     Ascii String List PArith ZArith.
From Coq Require Fin.
Import ListNotations.

From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.

From DeepWeb Require Import
     Lib.Util Lib.LinearSpec Spec.ServerDefs.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Section Spec.

Variable (app : App.t).

(** This is the main loop of the swap server.  The parameter [conns]
     maintains the list of open connections, while [last_msg] holds
     the message received from the last client (which will be sent
     back to the next client).  The server repeatedly chooses between
     accepting a new connection or doing a receive and then a send on
     some existing connection picked in the list [conns]. *)

CoFixpoint linear_spec'
           (conns : list connection_id)
           (s : App.state app)
  : itree specE unit :=
  or
    ( (* Accept a new connection. *)
      c <- obs_connect;;
      linear_spec' (c :: conns) s
    ) 
    ( (* Exchange a pair of messages on a connection. *)
      c <- choose conns;;
      req <- obs_msg_to_server (App.req_size app) c;;
      let '(s', resp) := App.app app (s, req) in
      obs_msg_from_server c resp;;
      linear_spec' conns s'
    ).

(* Top-level spec.  *)
Definition linear_spec :=
  linear_spec' [] (App.initial_state app).

End Spec.

Definition real_swap_spec := linear_spec real_swap_app.

(* A variant of the spec for testing, using shorter messages. *)
Definition test_swap_spec := linear_spec test_swap_app.
