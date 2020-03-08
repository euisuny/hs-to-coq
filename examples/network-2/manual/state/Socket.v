From Coq Require Import
     ZArith
     String
     List
     ProofIrrelevance.
Import ListNotations.

From Lib Require Import Util ITreePrelude.

From Lib Require Export Network SocketConstants.

Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Module SocketModel.

  Open Scope Z.

  (* Too abstract?? *)
  Parameter is_fd: Z -> Prop.
  Axiom fd_bound: forall i, is_fd i -> 0 <= i <= MAX_FD.
  Axiom zero_is_fd : is_fd 0.

  Record sockfd: Type :=
    { descriptor : Z;
      is_descriptor: is_fd descriptor }.

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

  Variant socket_status :=
  | ClosedSocket
  | OpenedSocket
  | BoundSocket (addr : endpoint_id)
  | ListeningSocket (addr : endpoint_id)
  | ConnectedSocket (conn : connection_id).

  Record SocketMap : Type :=
    { lookup_socket :> sockfd -> socket_status }.

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

  Definition update_socket_state
             (api_st: SocketMap)
             (fd : sockfd) (new_status: socket_status) :
    SocketMap :=
    {| lookup_socket fd' :=
         if Z.eqb (descriptor fd) (descriptor fd') then new_status
         else lookup_socket api_st fd';
    |}.

  Lemma lookup_update_socket_neq
        (api_st : SocketMap)
        (fd : sockfd) (new_status : socket_status)
        (fd' : sockfd):
    descriptor fd <> descriptor fd' ->
    lookup_socket (update_socket_state api_st fd new_status) fd' =
    lookup_socket api_st fd'.
  Proof.
    intros.
    unfold update_socket_state.
    simpl.
    destruct (descriptor fd =? descriptor fd') eqn:Heq.
    rewrite Z.eqb_eq in Heq;
      exfalso; apply H; auto.
    reflexivity.
  Qed.

  Lemma lookup_update_socket_eq
        (api_st : SocketMap)
        (fd : sockfd) (new_status : socket_status)
        (fd' : sockfd):
    descriptor fd = descriptor fd' ->
    lookup_socket (update_socket_state api_st fd new_status) fd' = new_status.
  Proof.
    intros.
    unfold update_socket_state.
    simpl.
    rewrite <- Z.eqb_eq in H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma lookup_update_socket_notIn
        (api_st : SocketMap)
        (fd : sockfd) (new_status : socket_status)
        (fds : list sockfd):
    ~In fd fds ->
    (forall fd', In fd' fds ->
            lookup_socket (update_socket_state api_st fd new_status) fd'
            = api_st fd').
  Proof.
    intros H.
    intros fd' fd'_in.
    rewrite lookup_update_socket_neq; trivial.
    unfold not; intro Hcontra.
    apply is_fd_irrelevant in Hcontra.
    subst fd.
    contradiction.
  Qed.

  Lemma lookup_update_socket_In
        (api_st : SocketMap)
        (fd : sockfd) (new_status : socket_status)
        (fds : list sockfd):
    In fd fds ->
    (forall fd', ~In fd' fds ->
            lookup_socket (update_socket_state api_st fd new_status) fd'
            = api_st fd').
  Proof.
    intros H.
    intros fd' fd'_in.
    rewrite lookup_update_socket_neq; trivial.
    unfold not; intro Hcontra.
    apply is_fd_irrelevant in Hcontra.
    subst fd.
    contradiction.
  Qed.

  Lemma socket_extensionality (api_st1 api_st2 : SocketMap):
    (forall fd, lookup_socket api_st1 fd = lookup_socket api_st2 fd) ->
    api_st1 = api_st2.
  Proof.
    intros Hlookup.
    destruct api_st1, api_st2.
    f_equal.
    apply functional_extensionality.
    intros fd'.
    apply Hlookup; auto.
  Qed.

  Lemma restore_update_socket
        (api_st0 : SocketMap)
        (fd : sockfd) (st st' : socket_status):
    lookup_socket api_st0 fd = st ->
    let api_st1 := update_socket_state api_st0 fd st' in
    let api_st2 := update_socket_state api_st1 fd st in
    api_st0 = api_st2.
  Proof.
    intros Hst.
    apply socket_extensionality.
    intros fd'.
    destruct (descriptor fd =? descriptor fd') eqn:Hfd.
    {
      apply Z.eqb_eq in Hfd.
      pose proof Hfd as Hfd'.
      apply lookup_descriptor with (api_st := api_st0) in Hfd.
      rewrite lookup_update_socket_eq by assumption.
      subst.
      rewrite Hfd.
      reflexivity.
    }

    apply Z.eqb_neq in Hfd.
    rewrite lookup_update_socket_neq by assumption.
    rewrite lookup_update_socket_neq by assumption.
    trivial.
  Qed.

  Lemma update_socket_id
        (api_st : SocketMap) (fd : sockfd):
    api_st = update_socket_state api_st fd (lookup_socket api_st fd).
  Proof.
    intros.
    unfold update_socket_state, lookup_socket.
    destruct api_st eqn:Hst.
    f_equal.
    apply functional_extensionality.
    intros fd'.
    destruct (descriptor fd =? descriptor fd') eqn:Heq; auto.
    rewrite Z.eqb_eq in Heq.
    apply lookup_descriptor with (api_st := api_st) in Heq.
    subst.
    auto.
  Qed.

  Definition consistent_world (api_st : SocketMap) :=
    forall fd1 fd2 id1 id2,
      lookup_socket api_st fd1 = ConnectedSocket id1 ->
      lookup_socket api_st fd2 = ConnectedSocket id2 ->
      fd1 <> fd2 -> id1 <> id2.

  Lemma consistent_world_monotone
        (api_st: SocketMap) (st: socket_status):
    consistent_world api_st ->
    ~(exists id, st = ConnectedSocket id) ->
    forall fd, consistent_world (update_socket_state api_st fd st).
  Proof.
    intros Hconsistent Hstatus fd
           fd1 fd2 id1 id2
           Hlookup1 Hlookup2 fd_neq.

    destruct (descriptor fd =? descriptor fd1) eqn:Hfd1.
    {
      pose proof Hfd1 as fds_eq.
      rewrite Z.eqb_eq in fds_eq.
      apply is_fd_irrelevant in fds_eq.
      simpl in Hlookup1.
      rewrite Hfd1 in *.
      subst.
      exfalso.
      apply Hstatus.
      exists id1.
      reflexivity.
    }

    destruct (descriptor fd =? descriptor fd2) eqn:Hfd2.
    {
      pose proof Hfd2 as fds_eq.
      rewrite Z.eqb_eq in fds_eq.
      apply is_fd_irrelevant in fds_eq.
      simpl in Hlookup2.
      rewrite Hfd2 in *.
      subst.
      exfalso.
      apply Hstatus.
      exists id2.
      reflexivity.
    }

    rewrite Z.eqb_neq in *.

    rewrite lookup_update_socket_neq in *; auto.
    eauto.
  Qed.

End SocketModel.

(*
Module SocketE.
  Definition socketE : Type -> Type := (nondetE +' failureE +' networkE).

  Instance socketE_networkE : networkE -< socketE.
  constructor.
  intros.
  unfold socketE.
  apply inr1.
  apply inr1.
  trivial.
  Defined.

  Instance socketE_nondetE: nondetE -< socketE.
  repeat constructor; trivial.
  Defined.

  Instance socketE_failureE: failureE -< socketE.
  constructor.
  intros.
  apply inr1.
  apply inl1.
  trivial.
  Defined.

End SocketE.
 *)

Module FDSet.

  Import SocketModel.

  Definition FD_Set : Type := list sockfd.

  Definition insert_fd (fd : sockfd) (set : FD_Set) : FD_Set :=
    if List.existsb (fd_eqb fd) set
    then set
    else (fd :: set).

  Definition remove_fd (fd : sockfd) (set : FD_Set) : FD_Set :=
    List.filter (fun fd' => negb (fd_eqb fd fd')) set.

  Definition fd_subset (fdset1 fdset2 : FD_Set) : Prop :=
    List.incl (List.map descriptor fdset1)
              (List.map descriptor fdset2).

  Lemma fd_subset_refl:
    forall (fd_set : FD_Set), fd_subset fd_set fd_set.
  Proof.
    intros; unfold fd_subset; apply incl_refl.
  Qed.

  Lemma fd_subset_trans:
    forall (fd_set1 fd_set2 fd_set3: FD_Set),
      fd_subset fd_set1 fd_set2 ->
      fd_subset fd_set2 fd_set3 ->
      fd_subset fd_set1 fd_set3.
  Proof.
    unfold fd_subset; intros; eapply incl_tran; eassumption.
  Qed.

  Lemma fd_subset_insert1:
    forall (fd_set1 fd_set2 : FD_Set) (fd : sockfd),
      fd_subset fd_set1 fd_set2 ->
      In (descriptor fd) (map descriptor fd_set2) ->
      fd_subset (insert_fd fd fd_set1) fd_set2.
  Proof.
    intros.
    unfold insert_fd.
    destruct (existsb (fd_eqb fd)); trivial.
    unfold fd_subset.
    simpl.
    apply incl_cons; trivial.
  Qed.

  Lemma fd_subset_insert2:
    forall (fd_set1 fd_set2 : FD_Set) (fd : sockfd),
      fd_subset fd_set1 fd_set2 ->
      fd_subset fd_set1 (insert_fd fd fd_set2).
  Proof.
    intros; unfold insert_fd; destruct (existsb (fd_eqb fd)); trivial.
    unfold fd_subset in *.
    simpl.
    apply incl_tl; assumption.
  Qed.

End FDSet.

Module SockAddr.

  Record sockaddr :=
    { sin_family : Z ; sin_port : Z ; sin_addr : Z }.

End SockAddr.
