Generalizable Variable E.

From Coq Require Import
     ZArith
     String
     List
     ProofIrrelevance.
Import ListNotations.

From DeepWeb.Free.Monad Require Import
     Free Common Eq.Utt.
Import MonadNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SocketConstants.
Require Export DeepWeb.Lib.NetworkInterface.

Set Bullet Behavior "Strict Subproofs".

Module SocketAPI.

  Open Scope Z.
  
  Parameter is_fd: Z -> Prop.
  Axiom fd_nonneg: forall i : Z, is_fd i -> i < 0 -> False.
  Axiom fd_bound: forall i, is_fd i -> 0 <= i <= MAX_FD.
  Axiom zero_is_fd : is_fd 0.

  Record sockfd: Type :=
    { descriptor: Z; is_descriptor: is_fd descriptor }.

  Definition fd_eqb (fd1 fd2 : sockfd) : bool :=
    descriptor fd1 =? descriptor fd2.

  Lemma is_fd_irrelevant: forall fd1 fd2,
      descriptor fd1 = descriptor fd2 -> fd1 = fd2.
  Proof.
    intros [] [] Heqb.
    simpl in Heqb.
    pose proof proof_irrelevance.
    subst.
    specialize (H (is_fd descriptor1) is_descriptor0 is_descriptor1).
    subst.
    reflexivity.
  Qed.
      
  Definition socketE : Type -> Type := (nondetE +' failureE +' networkE).

  Instance socketE_networkE : networkE -< socketE.
  constructor.
  intros.
  unfold socketE.
  apply inr.
  trivial.
  Defined.

  Instance socketE_nondetE: nondetE -< socketE.
  repeat constructor; trivial.
  Defined.

  Instance socketE_failureE: failureE -< socketE.
  constructor.
  intros.
  apply inl.
  apply inr.
  trivial.
  Defined.

  Inductive socket_status :=
  | ClosedSocket
  | OpenedSocket
  | BoundSocket (addr : endpoint_id)
  | ListeningSocket (addr : endpoint_id)
  | ConnectedSocket (conn : connection_id).

  Record SocketMap : Type :=
    { lookup_socket: sockfd -> socket_status }.
  
  Lemma lookup_descriptor:
    forall (api_st : SocketMap) (fd1 fd2 : sockfd),
      descriptor fd1 = descriptor fd2 -> 
      lookup_socket api_st fd1 = lookup_socket api_st fd2.
  Proof.
    intros ? ? ? H.
    apply is_fd_irrelevant in H.
    subst.
    reflexivity.
  Qed.
  
  Definition connection_of_fd (api_st: SocketMap) (fd : sockfd)
    : option connection_id := 
    match lookup_socket api_st fd with
    | ConnectedSocket conn => Some conn
    | _ => None
    end.

  Definition endpoint_of_fd (api_st: SocketMap) (fd : sockfd)
    : option endpoint_id := 
    match lookup_socket api_st fd with
    | BoundSocket addr => Some addr
    | ListeningSocket addr => Some addr
    | _ => None
    end.
  
End SocketAPI.
