(* Some general facts about [itree] and
   proof rules for [nrefines_].

   - monad laws and equivalences involving nondeterminism;
   - [simplify_*] lemmas: equivalences to handle [simplify_network]
     (this function translates the effects actually used in the
     impl. model to those in the part of this codebase related
     to network refinement; it is a monad homomorphism);
   - [nrefines_*] lemmas: "proof rules" for [nrefines_],
     with the interesting ones being [nrefines_recv_byte_],
     [nrefines_send_byte_], [nrefines_accept_], [nrefines_while_]. *)

From Coq Require Import
     String
     Lia
     ZArith
     Relations
     Wellfounded.

From QuickChick Require Import
     Decidability.

Require Import ProofIrrelevance.

From Custom Require Import
     List.
Import ListNotations.

From DeepWeb.Free.Monad
     Require Import Free Common Hom Eq.Eq Eq.Stutter.
Open Scope itree_scope.

From DeepWeb Require Import
     Lib.NetworkAdapter
     Lib.NetworkInterface
     Lib.LinearSpec
     Lib.Util
     Spec.Swap_LinearSpec
     Spec.Swap_ImplModel.

Import SocketInterface.SocketAPI.
Import LinearSpec_Server.

Require Import DeepWeb.Proofs.Linear.Refines.

Close Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

(* * General facts about [itrees] *)

(* Most of these are actually proved in the [Free.Monad] library
   packaged with this experiment, but they are specialized here
   to avoid issues with type classes. *)

Lemma simplify_ret A (x : A) :
  @eq (itree implE _)
      (simplify_network (Ret x))
      (Ret x).
Proof.
  rewrite (match_itree (simplify_network _)).
  reflexivity.
Qed.

Module Import Stutter.

Notation "a ::> b" := (stutter a b) (at level 80) : stutter_scope.
Local Open Scope stutter_scope.

Lemma bind_bind E A B C
      (t : itree E A) (k1 : A -> itree E B) (k2 : B -> itree E C) :
  ((t >>= k1) >>= k2) ::> t >>= (fun x => k1 x >>= k2).
Proof.
  apply Stutter.eq_itree_stutter.
  apply Eq.bind_bind.
Qed.

Lemma or_bind E A B `{nondetE -< E} (t1 t2 : itree E A) (k : A -> itree E B) :
    (or t1 t2 >>= k) ::> (or (t1 >>= k) (t2 >>= k)).
Proof.
  simpl.
  rewrite bind_def.
  simpl.
  unfold or.
  constructor.
  intros []; apply stutter_refl.
Qed.

Lemma ret_bind E A B (a : A) (k : A -> itree E B) :
  (Ret a >>= k) ::> k a.
Proof.
  simpl; rewrite ret_bind.
  apply stutter_once.
Qed.

Lemma bind_bind0 E A B C
      (t : itree E A) (k1 : A -> itree E B) (k2 : B -> itree E C) :
  ((t >>= k1) >>=0 k2) ::> t >>= (fun x => k1 x >>=0 k2).
Proof.
  apply Stutter.eq_itree_stutter.
  simpl.
  unfold bind_itree.
  etransitivity.
  - apply Eq.core_bind_bind.
  - apply Eq.core_bind_mor.
    + reflexivity.
    + intro.
      rewrite core_bind_def.
      reflexivity.
Qed.

Lemma or_bind0 E A B `{nondetE -< E} (t1 t2 : itree E A) (k : A -> itree E B) :
    (or t1 t2 >>=0 k) ::> (or (t1 >>=0 k) (t2 >>=0 k)).
Proof.
  rewrite core_bind_def.
  simpl.
  unfold or.
  constructor.
  intros []; apply stutter_refl.
Qed.

Definition E1 := failureE +' nondetE +' serverE.

Lemma simplify_bind A B (t : itree _ A) (k : A -> itree _ B) :
  @eq_itree E1 B
           (simplify_network (t >>= k))
           (simplify_network t >>= fun x => simplify_network (k x)).
Proof.
  unfold simplify_network.
  rewrite hom_bind.
  reflexivity.
Qed.

Lemma simplify_or A (t1 t2 : itree _ A) :
  @stutter E1 A
    (simplify_network (or t1 t2))
    (or (simplify_network t1) (simplify_network t2)).
Proof.
  unfold simplify_network.
  rewrite hom_def; simpl.
  rewrite bind_def; simpl.
  constructor.
  intro x.
  rewrite bind_def.
  simpl.
  constructor.
  destruct x; apply Stutter.stutter_refl.
Qed.

Lemma simplify_choose A (xs : list A) :
  @stutter E1 A
           (simplify_network (choose xs))
           (choose xs).
Proof.
  unfold simplify_network.
  induction xs; rewrite hom_def; simpl.
  - rewrite bind_def.
    constructor.
    intros [].
  - rewrite bind_def.
    constructor.
    intro b.
    rewrite bind_def.
    constructor.
    destruct b.
    + fold (@simplify_network E1 _ _ _ A).
      rewrite simplify_ret.
      apply stutter_refl.
    + apply IHxs.
Qed.

Lemma simplify_fail A err :
  @stutter E1 A
           (simplify_network (fail err))
           (fail err).
Proof.
  unfold simplify_network.
  rewrite hom_def; simpl.
  rewrite bind_def; simpl.
  constructor.
  intros [].
Qed.

Lemma simplify_listen e :
  @stutter E1 _
           (simplify_network (listen e))
           (Ret tt).
Proof.
  unfold simplify_network.
  rewrite hom_def; simpl.
  rewrite bind_def; simpl.
  constructor.
  fold (@simplify_network E1 _ _ _).
  rewrite simplify_ret.
  apply stutter_refl.
Qed.

Lemma simplify_loop_with_state {S void} (body : S -> itree _ S) (s : S) :
  @stutter E1 void
           (simplify_network (loop_with_state body s))
           (loop_with_state (fun s' => simplify_network (body s')) s).
Proof.
  unfold simplify_network.
  apply Stutter.eq_itree_stutter.
  apply hom_loop_with_state.
Qed.

Lemma stutter_refl E R (t : itree E R) : t ::> t.
Proof.
  apply Stutter.stutter_refl.
Qed.
        
End Stutter.

(* * Proof rules for [nrefines_] *)

(* A small auxiliary lemma. *)
Lemma network_reordered_server_transitions:
  forall tr tr' ctr ns ns', server_transitions tr ns ns' -> 
                       network_reordered_ ns' tr' ctr ->
                       network_reordered_ ns (tr ++ tr')%list ctr.
Proof.
  induction tr; intros tr' ctr ns ns' Htransition Hreordere.
  - simpl.
    unfold server_transitions in Htransition;
      simpl in Htransition;
      subst.
    auto.
  - simpl.
    unfold server_transitions in Htransition;
      simpl in Htransition.
    destruct Htransition as [next_ns [transit_next transit_rest]].
    eapply ScrambleServer; [apply transit_next |].
    eapply IHtr; [apply transit_rest | ].
    assumption.
Qed.

(**)

Lemma nrefines_network_transition_ z s obs' ns' t
      (dtr : real_trace) :
  let s' := set_ns ns' (set_observer obs' s) in
  (forall dtr' : real_trace,
      is_spec_trace obs' dtr' ->
      is_spec_trace (get_spec s)
                        ((dtr ++ dtr')%list : real_trace)) ->
  server_transitions dtr (get_ns s) ns' ->
  nrefines_ z s' t ->
  nrefines_ z s t.
Proof.
  simpl.
  intros IH Htransition Hnrefines_obs'.
  unfold nrefines_ in *.
  intros tr [tr_open tr_in].
  destruct (Hnrefines_obs' tr (conj tr_open tr_in)) as
      [dstr [dstr_tr dstr_obs']].
  exists (dtr ++ dstr)%list.
  split; auto.
  eapply network_reordered_server_transitions; eauto.
Qed.
  
(**)

Lemma nrefines_monotonic z z' s t:
  nrefines_ z' s t -> z' > z ->
  nrefines_ z  s t.
Proof.
  intros H Hz.
  unfold nrefines_ in *.
  intros tr [Hopen Htrace];
    apply (fun J => H tr (conj Hopen J)).
  unfold is_impl_trace_ in *.
  eapply is_trace_monotonic; eassumption.
Qed.  

Lemma nrefines_or_ z s t1 t2 :
  nrefines_ z s t1 ->
  nrefines_ z s t2 ->
  nrefines_ z s (or t1 t2).
Proof.
  unfold nrefines_, or.
  intros H1 H2 tr [tr_open tr_trace].
  inversion_server_trace.
  - eexists; split; constructor.
  - apply inj_pair2 in H0;
      apply inj_pair2 in H5.
    subst.
    specialize (fun J => H1 _ (conj tr_open J)).
    specialize (fun J => H2 _ (conj tr_open J)).
    eapply is_trace_monotonic in H7; [| eauto].
    destruct x; [apply H1 | apply H2];
      rewrite from_to_serverE_trace;
      eassumption.
Qed.

Lemma nrefines_choose_ A z s
      (xs : list A) (k : A -> itree _ _) :
  (forall x, List.In x xs ->
             nrefines_ z s (k x)) ->
  nrefines_ z s (choose xs >>= k).
Proof.
  revert k. induction xs; intro k.
  - simpl. rewrite bind_def.
    intros _ tr [tr_open tr_trace]. simpl in tr_trace.
    inversion_server_trace.
    + eexists; split; constructor.
    + subst. destruct x.
  - intros H tr [tr_open tr_trace].
    unfold choose, or in tr_trace. simpl in tr_trace.
    rewrite bind_def in tr_trace. simpl in tr_trace.
    inversion_server_trace.
    + eexists; split; constructor.
    + apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      destruct x.
      * rewrite bind_def in H6. simpl in H6.
        inversion H6; subst.
        { eexists; split; constructor. }
        { specialize (H a).
          apply H; auto.
          { left; auto. }
          split; auto.
          apply (is_trace_monotonic z1); eauto.
          transitivity z0; auto.
          rewrite from_to_serverE_trace; auto.
        }
      * unfold nrefines_ in *.
        eapply IHxs; [|].
        intros. specialize (H x).
        eapply in_cons in H0. eapply H in H0. apply H0.
        split; try apply H1.
        split; auto.
        apply (is_trace_monotonic z0); eauto.
        rewrite from_to_serverE_trace; auto.
Qed.

Lemma nrefines_ret_ z s :
  nrefines_ z s (Ret tt).
Proof.
  unfold nrefines_. intros tr [tr_open tr_trace].
  inversion_server_trace.
  eexists; split; constructor.
Qed.

Lemma nrefines_fail_ A z s err (k : A -> _) :
  nrefines_ z s (fail err >>= k).
Proof.
  unfold nrefines_, fail. intros tr [tr_open tr_trace].
  simpl in tr_trace.
  rewrite bind_def in tr_trace.
  simpl in tr_trace.
  inversion_server_trace.
  - eexists; split; constructor.
  - destruct x.
Qed.

Theorem nrefines_recv_byte_ z s c k :
  (get_status s c = PENDING \/
   get_status s c = ACCEPTED) ->
  (forall b s',
      s' = append_inbytes c [b] s ->
      nrefines_ z s' (k b)) ->
  nrefines_ z s (simplify_network (Network.recv_byte c) >>= k).
Proof.
  unfold nrefines_.
  rewrite (match_itree (simplify_network _)). simpl.
  rewrite bind_def. simpl.
  intros Hstatus Hk tr [tr_open tr_trace].
  inversion_server_trace.
  { eexists; split; constructor. }
  destruct e0 as [ | c0 | ]; [inversion H0 | | inversion H0].
  simpl in H0, H3.
  apply inj_pair2 in H0; apply inj_pair2 in H3.
  inversion H0; subst c0.
  assert (empty_case :
            exists dstr, network_reordered_ (get_ns s) dstr [ToServer c x] /\
                         is_spec_trace (get_spec s) dstr).
  { exists []; split.
    * econstructor.
      simpl. unfold client_send.
      unfold get_status in Hstatus.
      destruct Hstatus as [Hstatus | Hstatus];
        rewrite Hstatus; reflexivity.
      constructor.
    * constructor. }
  subst k1. rewrite bind_def in H5. simpl in H5.
  inversion H5; subst tr0.
  { apply empty_case. }
  inversion H5.
  { apply empty_case. }
  rewrite bind_def in H9. simpl in H9.
  inversion H9.
  { apply empty_case. }
  subst.
  destruct tr_open as [Hc tr_open].
  edestruct Hk as [dstr [Hreordered Hdstr_trace]]; eauto.
  { split; eauto.
    apply (is_trace_monotonic z5).
    - lia.
    - rewrite from_to_serverE_trace; eauto.
  }
  exists dstr.
  split.
  - econstructor; eauto.
    { simpl. unfold client_send.
      unfold get_status in Hstatus.
      destruct Hstatus as [Hstatus | Hstatus];
        rewrite Hstatus; reflexivity. }
  - auto.
Qed.

Theorem nrefines_send_byte z s c b (k : itree implE unit):
  get_status s c = ACCEPTED ->
  List.prefix [b] (get_outbytes s c) ->
  let s' := drop_outbytes c 1 s in
  nrefines_ z s' k ->
  nrefines_ z s (simplify_network (Network.send_byte c b) >>= fun _ => k).
Proof.
  intros Hstatus b_in_head ns' Hk.
  unfold nrefines_ in *.
  intros tr [Hopen Htrace].
  simpl in Htrace.
  unfold Network.send_byte in Htrace; simpl in Htrace.
  unfold liftE in Htrace.
  unfold simplify_network in Htrace.
  rewrite hom_def in Htrace; simpl in Htrace.
  rewrite bind_bind in Htrace.
  rewrite bind_def in Htrace.
  simpl in Htrace.
  inversion_server_trace.
  { subst; exists []; split; constructor. }

  apply inj_pair2 in H0.
  apply inj_pair2 in H3.
  subst.
  simpl in *.

  rewrite ret_bind in H5.
  rewrite hom_ret in H5.
  rewrite ret_bind in H5.

  destruct Hopen as [c0_open tr0_open].
    
  destruct (fun J => Hk (from_serverE_trace tr0) (conj tr0_open J))
    as [dstr [reordered_dstr dstr_obs]].
  { rewrite from_to_serverE_trace; auto.
    eapply is_trace_monotonic; eauto. }

  exists dstr.
  split; auto.
  
  econstructor; eauto.

  unfold client_transition, client_recv.
  unfold get_status in Hstatus.
  rewrite Hstatus.
  subst ns'.
  revert c0_open.
  revert b_in_head.
  unfold get_outbytes.
  unfold Map.modify.
  intros [bytes conn_out]; rewrite conn_out; simpl.
  reflexivity.
Qed.

Lemma nrefines_accept_ _endpoint z s k :
  open_network_state s ->
  (forall c ns' s',
      ~get_is_open s c ->
      client_connect c (get_ns s) = Some (ns', tt) ->
      s' = set_is_open (fun c' => c = c' \/ get_is_open s c')
                       (set_ns ns' s) ->
      nrefines_ z s' (k c)) ->
  nrefines_ z s
    (simplify_network (Network.accept _endpoint) >>= k).
Proof.
  unfold nrefines_.
  intros Hns H tr [tr_open tr_trace].
  unfold Network.accept in tr_trace; simpl in tr_trace.
  unfold liftE in tr_trace; simpl in tr_trace.
  unfold simplify_network in tr_trace;
    rewrite hom_def in tr_trace;
    simpl in tr_trace.
  rewrite bind_bind in tr_trace.
  rewrite bind_def in tr_trace; simpl in tr_trace.
  inversion_server_trace.
  { eexists; split; constructor. }
  clear tr_trace.
  apply inj_pair2 in H1.
  apply inj_pair2 in H4.
  subst; simpl in *.
  rewrite ret_bind in H6.
  destruct tr_open as [H_nop tr_open].
  rename x into c.
  assert (Hstatus : get_status s c = CLOSED).
  { eapply co_open_network; eauto. }
  specialize (fun s' => H c (Map.update c pending_cs (get_ns s)) s' H_nop).
  unfold client_connect in H.
  unfold get_status in Hstatus.
  rewrite Hstatus in H.
  specialize (H _ eq_refl eq_refl).
  rewrite hom_ret in H6.
  rewrite ret_bind in H6.
  edestruct H as [dstr [Hreordered Hdstr_trace]]; eauto.
  { split; eauto.
    apply (is_trace_monotonic z0); eauto.
    rewrite from_to_serverE_trace. auto.
  }
  exists dstr.
  split.
  - econstructor.
    + simpl. unfold client_connect.
      rewrite Hstatus.
      reflexivity.
    + auto.
  - auto.
Qed.

Lemma nrefines_shutdown_not_implemented_ z s c k:
  nrefines_ z s (simplify_network (shutdown c) >>= k).
Proof.
  simpl; rewrite bind_def.
  intros tr [Hopen Htr].
  inversion_server_trace.
  - exists []. split; constructor.
  - destruct x.
Qed.
  
Definition loop_invariant A := state -> A -> Prop.

Lemma nrefines_tau_ z s t :
  (forall z',
      z' < z ->
      nrefines_ z' s t) ->
  nrefines_ z s (Tau t).
Proof.
  intros Hnrefines tr [Hopen Htr].
  inversion_server_trace.
  - exists [].
    split; constructor.
  - eapply Hnrefines; eauto.
    unfold is_impl_trace_.
    rewrite from_to_serverE_trace.
    auto.
Qed.

Lemma nrefines_loop_ z s
      A (body : A -> _ A) (a : A)
      (inv : loop_invariant A) :
  inv s a ->
  (forall z' s' a' k1,
      inv s' a' ->
      (forall s'' a'',
          inv s'' a'' ->
          nrefines_ z' s'' (k1 a'')) ->
      nrefines_ z' s' (body a' >>=0 k1)) ->
  nrefines_ z s (loop_with_state body a).
Proof.
  pose proof (lt_wf z) as strong_z. (* Prepare induction. *)
  intros Hinv Hbody.
  generalize dependent a.
  generalize dependent s.
  (* Strong induction on z *)
  induction strong_z as [z Hacc IH].
  intros s a Hinv.
  specialize Hbody with (a' := a).
  rewrite loop_with_state_unfold; simpl.
  apply Hbody; auto.
  intros s' a' Hinv'.
  apply nrefines_tau_.
  intros z' Hz'.
  apply IH; assumption.
Qed.

Ltac auto_simplify t :=
  match t with
  | (_ >>= _) >>= _ => rewrite bind_bind
  | (_ >>= _) >>=0 _ => rewrite bind_bind0
  | Ret _ >>=0 _ => rewrite ret_bind0
  | or _ _ >>=0 _ => rewrite or_bind0
  | @or ?E _ _ _ _ >>= _ => rewrite (or_bind E)
  | @Ret ?E _ _ >>= _ => rewrite (ret_bind E)
  | ?t1 >>= _ => auto_simplify t1
  | ?t1 >>=0 _ => auto_simplify t1
  | ?t1 >>= (fun _ => ?t2) => auto_simplify t1 + auto_simplify t2
  | simplify_network (_ >>= _) => rewrite simplify_bind
  | simplify_network (Ret _) => rewrite simplify_ret
  | simplify_network (or _ _) => rewrite simplify_or
  | or ?t1 ?t2 => auto_simplify t1 + auto_simplify t2
  end.

Ltac auto_simplify_nrefines1 :=
  match goal with
  | [ |- nrefines_ _ _ ?t ] => auto_simplify t
  end.

Ltac auto_simplify_nrefines := simpl; repeat auto_simplify_nrefines1.
