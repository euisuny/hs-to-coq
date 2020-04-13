(* Effectful computations from the Network.Socket library. *)
From ITree Require Import ITree.
Require Import NetworkTypes.
Require Import IO.
Require Import StringLib.
From Coq Require Import Strings.String.
Require Import GHC.Char.

Require Import NArith.

Fixpoint string_hs__ (s : Base.String) : string :=
  match s with
  | nil => EmptyString
  | cons c s  => String (ascii_of_nat (N.to_nat c)) (string_hs__ s)
  end.

Coercion Base.hs_string__ : string >-> Base.String.
Coercion string_hs__ : Base.String >-> string.

Section NetworkEmbed.


  Definition send : Socket -> Base.String -> IO Num.Int :=
    fun s x => embed (SendE s x).

  Definition close : Socket -> IO unit :=
    fun s => embed (CloseE s).

  Definition accept : Socket -> IO (Socket * SockAddr) :=
    fun s => embed (AcceptE s).

  Definition listen : Socket -> Num.Int -> IO unit :=
    fun s x => embed (ListenE s x).

  Definition bind : Socket -> SockAddr -> IO unit :=
    fun s x => embed (BindE s x).

  Definition setSocketOption :
    Socket -> SocketOption -> Num.Int -> IO unit :=
    fun s x y => embed (SetSocketOptionE s x y).

  Definition socket : Family -> SocketType -> Num.Int -> IO Socket :=
    fun f s x => embed (SocketE f s x).

End NetworkEmbed.
