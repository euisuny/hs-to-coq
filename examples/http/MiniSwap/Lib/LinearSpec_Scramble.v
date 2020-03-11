(* Scrambling: reordering (or "disordering") of a trace generated
   by a server into a trace observed by a client. *)

From QuickChick Require Import QuickChick.

From Coq Require Import RelationClasses.

From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.LinearSpec_NetworkModel
     Lib.LinearSpec_Traces.

Set Bullet Behavior "Strict Subproofs".

(* Main facts about [network_reordered] *)
Module Type ScramblingTypes.

(* This predicates defines "well-formed" traces, where
   connections must be open before messages can be sent on them. *)
Parameter wf_trace : forall {byte'}, list (event byte') -> Prop.

(* We restrict the relation [network_reordered] to well-formed
   traces, by making this vacuously true on bad traces. *)
Definition network_reordered_wf_ ns (tr0 tr1 : real_trace) :=
  wf_trace tr0 ->
  wf_trace tr1 ->
  network_reordered_ ns tr0 tr1.

(* We consider reorderings of well-formed traces from the
   initial state. *)
Definition network_reordered_wf := network_reordered_wf_ initial_ns.

(* Then [network_reordered_wf0] is reflexive. *)
Declare Instance reordered_reflexive : Reflexive network_reordered_wf.

(* And [network_reordered0] is transitive. *)
Declare Instance reordered_transitive : Transitive network_reordered.

(* Note that the "well-formedness" precondition is implicit
   in the two preconditions of transitivity. *)
Parameter reordered_implies_wf : forall tr str : real_trace,
    network_reordered tr str ->
    wf_trace tr /\ wf_trace str.

End ScramblingTypes.

(* The proof of transitivity is monstrous, so we postpone it
   to [LinearSpec_ScrambleTransitivity.v]. *)
Module Type ScrambleTransitivityType.
(* And [network_reordered0] is transitive. *)
Declare Instance reordered_transitive : Transitive network_reordered.
End ScrambleTransitivityType.

Module ScramblingFacts (Transitivity : ScrambleTransitivityType)
  <: ScramblingTypes.

Include Transitivity.

Definition project_trace_on {byte'} (c : connection_id) :
  list (event byte') -> list (event byte') :=
  filter (fun ev => event_connection ev = c ?).

Definition is_ToFromServer {byte'} (ev : event byte') : bool :=
  match ev with
  | NewConnection _ => false
  | ToServer _ _ | FromServer _ _ => true
  end.

Definition wf_projection {byte'} (tr : list (event byte')) : bool :=
  match tr with
  | [] => true
  | NewConnection _ :: tr' =>
    forallb is_ToFromServer tr'
  | (ToServer _ _ | FromServer _ _) :: _ => false
  end.

Definition wf_trace {byte'} (tr : list (event byte')) : Prop :=
  forall c,
    is_true (wf_projection (project_trace_on c tr)).

Definition open_network
           (is_open : connection_id -> Prop)
           (ns : network_state) : Prop :=
  forall c, is_open c <->
            (connection_status (Map.lookup ns c) = PENDING \/
             connection_status (Map.lookup ns c) = ACCEPTED).

Lemma co_open_network is_open ns :
  open_network is_open ns ->
  forall c, ~is_open c <->
            connection_status (Map.lookup ns c) = CLOSED.
Proof.
  intros H c.
  specialize (H c).
  split; intro Hc.
  - destruct connection_status; [reflexivity| | ];
      exfalso; apply Hc; apply H; [left | right]; reflexivity.
  - rewrite H.
    intros [H' | H'];
      rewrite Hc in H';
      discriminate H'.
Qed.

Lemma modify_open_network_
      (is_open : connection_id -> Prop)
      (is_open' : connection_id -> Prop)
      (ns : network_state)
      (c : connection_id)
      (f : connection_state -> connection_state) :
  open_network is_open ns ->
  (is_open' c <->
   (connection_status (f (Map.lookup ns c)) = PENDING \/
    connection_status (f (Map.lookup ns c)) = ACCEPTED)) ->
  (forall c', c <> c' -> is_open c' <-> is_open' c') ->
  open_network is_open' (Map.modify c f ns).
Proof.
  intros Hns Hc Hc' c'.
  specialize (Hc' c').
  unfold Map.modify.
  destruct (eqb_connection_id c c').
  - subst c'; rewrite Map.update_lookup_eq by reflexivity; auto.
  - rewrite <- Hc' by auto.
    rewrite Map.update_lookup_neq by auto.
    auto.
Qed.

Lemma modify_open_network_open
      (is_open : connection_id -> Prop)
      (ns : network_state)
      (c : connection_id)
      (f : connection_state -> connection_state) :
  open_network is_open ns ->
  is_open c ->
  (connection_status (f (Map.lookup ns c)) = PENDING \/
   connection_status (f (Map.lookup ns c)) = ACCEPTED) ->
  open_network is_open (Map.modify c f ns).
Proof.
  intros Hns Hc Hc_.
  eapply modify_open_network_; eauto.
  split; auto.
  intros; reflexivity.
Qed.

Lemma modify_open_network_connect
      (is_open : connection_id -> Prop)
      (ns : network_state)
      (c : connection_id)
      (f : connection_state -> connection_state) :
  open_network is_open ns ->
  (connection_status (f (Map.lookup ns c)) = PENDING \/
   connection_status (f (Map.lookup ns c)) = ACCEPTED) ->
  open_network (fun c' => c' = c \/ is_open c')
               (Map.modify c f ns).
Proof.
  intros Hns Hc.
  eapply modify_open_network_; eauto.
  - split.
    + auto.
    + left; auto.
  - intuition.
Qed.

Fixpoint open_trace {byte'}
         (is_open : connection_id -> Prop) (tr : list (event byte')) :
  Prop :=
  match tr with
  | [] => True
  | NewConnection c :: tr =>
    ~is_open c /\ open_trace (fun c' => c = c' \/ is_open c') tr
  | (ToServer c _ | FromServer c _) :: tr =>
    is_open c /\ open_trace is_open tr
  end.

Lemma open_trace_prop {byte'}
           (is_open is_open' : _) (tr : list (event byte')) :
  open_trace is_open tr ->
  (forall c, is_open c <-> is_open' c) ->
  open_trace is_open' tr.
Proof.
  generalize dependent is_open.
  generalize dependent is_open'.
  induction tr as [ | [ c | c b | c b] tr ];
    intros is_open is_open' Htr_open Hopen.
  - auto.
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      { intro c0.
        split; intros [Hc0 | Hc0];
          auto;
          right; apply Hopen; auto.
      }
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      auto.
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      auto.
Qed.

Lemma wf_open {byte'} :
  forall (tr : list (event byte')) (is_open : _ -> Prop),
    (forall c,
        (is_open c /\
         is_true (forallb is_ToFromServer (project_trace_on c tr))) \/
        (~is_open c /\
         is_true (wf_projection (project_trace_on c tr)))) ->
    open_trace is_open tr.
Proof.
  induction tr; intros.
  - constructor.
  - simpl. destruct a.
    + split.
      * destruct (H c) as [H0 | H0].
        { destruct H0 as [? Hc]; simpl in Hc.
          destruct eqb_connection_id.
          - discriminate Hc.
          - exfalso; auto. }
        { apply H0. }
      * apply IHtr; auto.
        intro c0.
        destruct (H c0) as [H0 | H0].
        { simpl in H0; destruct H0.
          destruct eqb_connection_id.
          - discriminate.
          - left; auto. }
        { simpl in H0; destruct H0.
          destruct eqb_connection_id.
          - subst c0. simpl in H1.
            left; auto.
          - right; split; auto.
            intros []; auto. }
    + split.
      * destruct (H c) as [H0 | H0].
        { apply H0. }
        { destruct H0. simpl in H1. destruct eqb_connection_id in H1.
          { discriminate. } { contradiction. } }
      * apply IHtr.
        intro c0.
        destruct (H c0) as [[? H0] | [? H0]].
        { simpl in H0. destruct eqb_connection_id; auto. }
        { simpl in H0. destruct eqb_connection_id; auto; discriminate.
        }
    + split.
      * destruct (H c) as [H0 | H0].
        { apply H0. }
        { destruct H0. simpl in H1. destruct eqb_connection_id in H1.
          { discriminate. } { contradiction. } }
      * apply IHtr.
        intro c0.
        destruct (H c0) as [[? H0] | [? H0]].
        { simpl in H0. destruct eqb_connection_id; auto. }
        { simpl in H0. destruct eqb_connection_id; auto; discriminate.
        }
Qed.

Lemma open_wf {byte'} :
  forall (c : connection_id)
         (tr : list (event byte')) (is_open : _ -> Prop),
    ~is_open c ->
    open_trace is_open tr ->
    is_true (wf_projection (project_trace_on c tr)).
Proof.
  intro c.
  induction tr.
  + intros. auto.
  + simpl. intros.
    destruct a; simpl; destruct eqb_connection_id; simpl.
    * { subst. simpl.
        remember (fun c' => c = c' \/ is_open c') as is_open' eqn:e_is_open'.
        assert (Hopen' : is_open' c).
        { rewrite e_is_open'; left; reflexivity. }
        destruct H0 as [H0 Hopen].
        clear H0.
        clear e_is_open'.
        generalize dependent is_open'.
        clear IHtr.
        induction tr.
        - auto.
        - simpl; intros.
          destruct eqb_connection_id.
          { destruct a; simpl in *.
            - subst c0. exfalso. apply Hopen; auto.
            - subst c0.
              apply IHtr with (is_open' := is_open'); auto.
              apply Hopen.
            - subst c0.
              apply IHtr with (is_open' := is_open'); auto.
              apply Hopen. }
          { destruct a.
            - eapply IHtr with (is_open' := fun c' => c0 = c' \/ is_open' c'); auto.
              apply Hopen.
            - eapply IHtr with (is_open' := is_open'); auto. apply Hopen.
            - eapply IHtr with (is_open' := is_open'); auto. apply Hopen.
          }
      }
    * { apply IHtr with (is_open := (fun c' => c0 = c' \/ is_open c')); auto.
        { intros []; auto. }
        apply H0.
      }
    * { subst c0. exfalso; apply H; apply H0. }
    * { apply IHtr with (is_open := is_open); auto.
        apply H0. }
    * { subst c0. exfalso; apply H; apply H0. }
    * { apply IHtr with (is_open := is_open); auto.
        apply H0. }
Qed.

Lemma equiv_open_wf {byte'} :
  forall (tr : list (event byte')),
    open_trace (fun _ => False) tr <-> wf_trace tr.
Proof.
  intros.
  split; intros H.
  - intro c. eapply open_wf; eauto. simpl; auto.
  - apply wf_open; auto.
Qed.

Lemma reordered_implies_open :
  forall (ns : network_state) is_open is_open2 (tr str : real_trace),
    (forall c, is_open c <->
               connection_status (Map.lookup ns c) = ACCEPTED) ->
    (forall c, is_open2 c <->
               connection_status (Map.lookup ns c) = PENDING \/
               connection_status (Map.lookup ns c) = ACCEPTED) ->
    network_reordered_ ns tr str ->
    open_trace is_open tr /\ open_trace is_open2 str.
Proof.
  intros ns is_open1 is_open2 tr str Hopen1 Hopen2 Hreordered.
  generalize dependent is_open2.
  generalize dependent is_open1.
  induction Hreordered; intros is_open1 Hopen1 is_open2 Hopen2.
  { (* No transition *)
    repeat constructor. }

  { (* Server transition *)
    destruct e eqn:case_e; simpl in *.
    - (* Accept *)
      rewrite Hopen1.
      unfold server_accept in H.
      destruct (connection_status (Map.lookup ns c)) eqn:Hstatus;
        try discriminate.
      inversion H; subst ns'.
      specialize IHHreordered with
        (is_open1 := fun c' => c = c' \/ is_open1 c')
        (is_open2 := is_open2).
      destruct IHHreordered.
      { intro c0.
        rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { rewrite Map.update_lookup_eq by auto.
          tauto. }
        { rewrite Map.update_lookup_neq by auto.
          tauto.
        }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0.
          rewrite Map.update_lookup_eq by auto.
          tauto. }
        { rewrite Map.update_lookup_neq by auto.
          tauto. }
      }
      repeat split; try discriminate; auto.

    - (* Server-side ToServer *)
      rewrite Hopen1.
      specialize IHHreordered with
        (is_open1 := is_open1) (is_open2 := is_open2).
      unfold server_recv in H.
      destruct connection_status eqn:Hstatus;
        try discriminate H.
      destruct connection_inbytes eqn:Hbytes in H;
        try discriminate H.
      inversion H; subst ns' b0.
      destruct IHHreordered.
      { intro c0. rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto; reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto. reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      repeat split; try discriminate; auto.


    - (* Server-side ToServer *)
      rewrite Hopen1.
      specialize IHHreordered with
        (is_open1 := is_open1) (is_open2 := is_open2).
      unfold server_send in H.
      destruct connection_status eqn:Hstatus;
        try discriminate H.
      inversion H; subst ns'.
      destruct IHHreordered.
      { intro c0. rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto; reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto. reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      repeat split; try discriminate; auto.
  }

  { (* Client transition *)
    destruct e eqn:case_e; simpl in *.
    - (* Connect *)
      rewrite Hopen2.
      unfold client_connect in H.
      destruct (connection_status (Map.lookup ns c)) eqn:Hstatus;
        try discriminate.
      inversion H; subst ns'.
      specialize IHHreordered with
        (is_open1 := is_open1)
        (is_open2 := fun c' => c = c' \/ is_open2 c').
      destruct IHHreordered.
      { intro c0.
        rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { subst c0.
          rewrite Map.update_lookup_eq by auto.
          rewrite Hstatus.
          split; discriminate. }
        { rewrite Map.update_lookup_neq by auto. reflexivity.
        }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0.
          rewrite Map.update_lookup_eq by auto.
          tauto. }
        { rewrite Map.update_lookup_neq by auto.
          tauto. }
      }
      repeat split; auto.
      intros []; discriminate.

    - (* Client-side ToServer *)
      rewrite Hopen2.
      specialize IHHreordered with
        (is_open1 := is_open1) (is_open2 := is_open2).
      unfold client_send in H.
      assert (H' :
          (connection_status (Map.lookup ns c) = PENDING \/
           connection_status (Map.lookup ns c) = ACCEPTED) /\
          Some
            (Map.update c
               (update_in
                  (connection_inbytes (Map.lookup ns c) ++ [b])
                  (Map.lookup ns c)) ns, tt)
          = Some (ns', tt)).
      { destruct connection_status; try discriminate H; tauto. }
      clear H.
      destruct H' as [H Hns].
      inversion Hns; subst ns'; clear Hns.
      destruct IHHreordered.
      { intro c0. rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto; reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto. reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      repeat split; auto.

    - (* Client-side FromServer *)
      rewrite Hopen2.
      specialize IHHreordered with
        (is_open1 := is_open1) (is_open2 := is_open2).
      unfold client_recv in H.
      destruct connection_status eqn:Hstatus;
        try discriminate H.
      destruct connection_outbytes eqn:Hbytes in H;
        try discriminate H.
      inversion H; subst ns' b0.
      destruct IHHreordered.
      { intro c0. rewrite Hopen1.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto; reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      { intro c0.
        rewrite Hopen2.
        destruct (eqb_connection_id c c0).
        { subst c0; rewrite Map.update_lookup_eq by auto. reflexivity.
        }
        { rewrite Map.update_lookup_neq by auto. reflexivity. }
      }
      repeat split; try discriminate; auto.
  }
Qed.

Lemma reordered_implies_wf : forall tr str : real_trace,
    network_reordered tr str ->
    wf_trace tr /\ wf_trace str.
Proof.
  intros tr str Hreordere.
  do 2 rewrite <- equiv_open_wf.
  apply (reordered_implies_open initial_ns); auto.
  - intro c; split; [intros [] | discriminate].
  - intro c; split; [intros [] | intros []; discriminate].
Qed.

Definition network_reordered_wf_ ns (tr0 tr1 : real_trace) :=
  wf_trace tr0 ->
  wf_trace tr1 ->
  network_reordered_ ns tr0 tr1.

Definition network_reordered_wf := network_reordered_wf_ initial_ns.

Section ReflexivityProof.

(* The notion of "open" connection is not quite the same
   depending on whether we're on the client side or server side. *)

(* For a client, open connections are those that are
   [PENDING] or [ACCEPTED]. *)
Definition is_open_conns_client ns : connection_id -> Prop :=
  fun c =>
    connection_status (Map.lookup ns c)
    <> CLOSED.

(* For a server, open connections are those that it [ACCEPTED]. *)
Definition is_open_conns_server ns : connection_id -> Prop :=
  fun c =>
    connection_status (Map.lookup ns c) = ACCEPTED.

(* [clean_state ns] holds when all connections [ns]
   have empty buffers. *)
Definition clean_state (ns : network_state) := forall c,
    let cs := Map.lookup ns c in
    connection_status cs <> PENDING /\
    connection_inbytes  cs = [] /\
    connection_outbytes cs = [].

Definition bind_transition {S B}
           (a : option (S * unit)) (b : S -> option (S * B)) :
  option (S * B) :=
  match a with
  | Some (s, _) => b s
  | None => None
  end.

Lemma open_reordered_reflexive :
  forall ns tr,
    clean_state ns ->
    open_trace (is_open_conns_server ns) tr ->
    network_reordered_ ns tr tr.
Proof.
  intros ns tr.
  generalize dependent ns.
  induction tr as [ | [ c | c b | c b ] tr ];
    intros ns Hns_clean Htr_open.
  - (* [] *) constructor.
  - (* NewConnection c :: tr *)
    eapply ScrambleClient.
    { simpl. rewrite connect_success.
      { reflexivity. }
      { destruct Htr_open.
        unfold is_open_conns_server in H.
        destruct (Hns_clean c) as [ ? ? ].
        destruct connection_status; auto.
        exfalso; auto.
        exfalso; auto. }
    }
    eapply ScrambleServer.
    { simpl. rewrite accept_success.
      { reflexivity. }
      { destruct Htr_open.
        unfold is_open_conns_server in H.
        rewrite Map.update_lookup_eq; auto. }
    }
    unfold Map.modify.
    apply IHtr.
    + rewrite Map.update_update_eq by reflexivity.
      rewrite Map.update_lookup_eq by reflexivity.
      intro c0.
      destruct (@dec (c = c0)).
      { typeclasses eauto. }
      { rewrite Map.update_lookup_eq by assumption.
        simpl; split; auto; discriminate. }
      { rewrite Map.update_lookup_neq by assumption.
        apply Hns_clean. }
    + destruct Htr_open as [Htr0 Htr1].
      apply open_trace_prop with (1 := Htr1).
      intros c0.
      unfold is_open_conns_server.
      rewrite Map.update_update_eq by reflexivity.
      rewrite Map.update_lookup_eq with (1 := eq_refl).
      destruct (@dec (c = c0)).
      { typeclasses eauto. }
      { rewrite Map.update_lookup_eq by assumption.
        split; auto. }
      { rewrite Map.update_lookup_neq by assumption.
        split; auto.
        intros []; auto; contradiction. }

  - (* ToServer c b :: tr *)
    assert (connection_status (Map.lookup ns c) = ACCEPTED).
    { apply Htr_open. }
    eapply ScrambleClient.
    { simpl. unfold client_send. rewrite H.
      rewrite (proj1 (proj2 (Hns_clean _))).
      simpl.
      reflexivity. }
    eapply ScrambleServer.
    { simpl.
      unfold server_recv.
      rewrite Map.update_lookup_eq by reflexivity.
      simpl.
      rewrite H.
      rewrite Map.update_update_eq by reflexivity.
      reflexivity. }
    replace (update_in _ _) with (Map.lookup ns c).
    { erewrite Map.lookup_update_eq by reflexivity.
      apply IHtr.
      { assumption. }
      { apply Htr_open. } }
    { specialize (Hns_clean c).
      destruct Map.lookup; unfold update_in; simpl in *.
      f_equal.
      apply Hns_clean. }

  - (* FromServer c b :: tr *)
    assert (connection_status (Map.lookup ns c) = ACCEPTED).
    { apply Htr_open. }
    eapply ScrambleServer.
    { simpl. unfold server_send. rewrite H.
      rewrite (proj2 (proj2 (Hns_clean _))).
      simpl.
      reflexivity. }
    eapply ScrambleClient.
    { simpl.
      unfold client_recv.
      rewrite Map.update_lookup_eq by reflexivity.
      simpl.
      rewrite H.
      rewrite Map.update_update_eq by reflexivity.
      reflexivity. }
    replace (update_out _ _) with (Map.lookup ns c).
    { erewrite Map.lookup_update_eq by reflexivity.
      apply IHtr.
      { assumption. }
      { apply Htr_open. } }
    { specialize (Hns_clean c).
      destruct Map.lookup; unfold update_out; simpl in *.
      f_equal.
      apply Hns_clean. }
Qed.

Global Instance reordered_reflexive : Reflexive network_reordered_wf.
Proof.
  unfold Reflexive.
  intros tr Htr_wf _H. clear _H.
  apply equiv_open_wf in Htr_wf.
  apply open_reordered_reflexive.
  { intro c; split; auto; discriminate. }
  { apply open_trace_prop with (1 := Htr_wf).
    unfold is_open_conns_server.
    simpl.
    split; discriminate + intros []. }
Qed.

End ReflexivityProof.

(* We can always add sends to the end of a trace. *)
Conjecture trailing_sends_preserve_reordered :
  forall ns tr str,
    network_reordered_ ns tr str ->
    forall tr' str',
      (* No [server_accept] or [server_recv]. *)
      is_true (forallb is_FromServer tr') ->
      (* No [client_recv] *)
      is_true (forallb (fun ev => negb (is_FromServer ev)) tr') ->
      (* Make sure the extended traces are well-formed. *)
      wf_trace (tr ++ tr') ->
      wf_trace (str ++ str') ->
      network_reordered_ ns (tr ++ tr') (str ++ str').

End ScramblingFacts.
