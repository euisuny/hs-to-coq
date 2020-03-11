(* Conversion from the effects used in the VST part
   to the simplified version used by LinearSpec. *)

From DeepWeb.Free.Monad Require Import
     Free Common Hom.
Import MonadNotations.
Import SumNotations.
Require Import String.
Open Scope string_scope.
From DeepWeb.Lib Require Import
     NetworkInterface
     LinearSpec_Server.

Module N0 := NetworkInterface.Network.
Module N1 := LinearSpec_Server.

Definition E0 := nondetE +' failureE +' N0.networkE.
Definition serverE1 := N1.ServerType.serverE.

Definition simplify_network' {E}
           `{failureE -< E} `{nondetE -< E} `{serverE1 -< E} :
  forall X, E0 X -> itree E X :=
  fun _ e =>
    match e with
    | (| e ) =>
      match e in N0.networkE X return itree E X with
      | N0.Listen _ => ret tt
      | N0.Accept _ => N1.accept
      | N0.RecvByte c => N1.recv_byte c
      | N0.SendByte c b => N1.send_byte c b
      | N0.Shutdown c => fail "not implemented"
      end
    | (| Fail reason |) => fail reason
    | ( _Or ||) => liftE (convert _Or)
    end.

Definition simplify_network {E}
           `{failureE -< E} `{nondetE -< E} `{serverE1 -< E} :
  forall X, itree E0 X -> itree E X :=
  hom simplify_network'.

Arguments simplify_network {E _ _ _} [X].
