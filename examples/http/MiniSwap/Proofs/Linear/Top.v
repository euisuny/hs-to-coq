(* Proof that the implementation model for the swap server
   "network refines" the linear specification.

   The main theorem we prove at the end of this file
   is [server_refines_swap]. The body of the main loop is
   handled in [nrefines_process_], showing that the invariant
   [select_loop_invariant'] is preserved.
 *)

From Coq Require Import
     String
     ZArith
     Setoid
     Morphisms
     Program
     Relations
     Wellfounded
     Lia.

Require Import ProofIrrelevance.

From QuickChick Require Import
     Decidability.

(* Require Import ProofIrrelevance. *)

From Custom Require Import
     List
     Monad.
Import MonadNotations.
Import ListNotations.
Open Scope monad_scope.

From DeepWeb.Free.Monad
     Require Import Free Common.

From DeepWeb Require Import
     Lib.NetworkAdapter
     Lib.NetworkInterface
     Lib.LinearSpec
     Lib.Util
     Spec.Swap_LinearSpec
     Spec.Swap_ImplModel
     Spec.ServerDefs
     Proofs.Linear.Refines
     Proofs.Linear.Util.

Import SocketInterface.SocketAPI.
Import LinearSpec_Server.

Open Scope list_scope.
Close Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Ltac split_and :=
  match goal with
  | [ |- _ /\ _ ] => split; try split_and
  end.

Section LinearizationProof.
Variable (app : App.t).

(* General facts about functions used for the swap server and spec. *)
Section GeneralFacts.

Lemma le_sub_add_le : forall a b c,
    (c <= b)%nat ->
    (a <= b - c)%nat ->
    (c + a <= b)%nat.
Proof. intros; lia. Qed.

Lemma has_conn_state_prop p c :
  conn_state c = p <-> has_conn_state p c = true.
Proof.
  destruct p, c as [? ? ? ? []]; split; simpl; intros H;
    discriminate + reflexivity.
Qed.

Lemma has_conn_state_RS c :
  conn_state c = RECVING \/ conn_state c = SENDING <->
  (has_conn_state RECVING c || has_conn_state SENDING c)%bool = true.
Proof.
  do 2 rewrite has_conn_state_prop.
  rewrite <- Bool.orb_true_iff.
  reflexivity.
Qed.

Lemma has_conn_state_DD c :
  conn_state c = DONE \/ conn_state c = DELETED <->
  (has_conn_state RECVING c || has_conn_state SENDING c)%bool = false.
Proof.
  destruct c as [? ? ? ? []]; simpl; split;
    auto + intros []; discriminate.
Qed.

Definition In_active c cs :=
  In c (filter (has_conn_state RECVING) cs ++
        filter (has_conn_state SENDING) cs).

Lemma In_active_cons c0 c cs :
  In_active c0 cs -> In_active c0 (c :: cs).
Proof.
  unfold In_active.
  intro H.
  apply in_app_or in H.
  apply in_or_app.
  repeat rewrite filter_In in *.
  destruct H as [[H1 H2] | [H1 H2]]; [left | right];
    (split; [right |]); auto.
Qed.

Definition is_active c :=
  conn_state c = RECVING \/ conn_state c = SENDING.

Definition unique_conn c cs : Prop :=
  forall c',
    In_active c' cs ->
    conn_id c' = conn_id c ->
    c' = c.

Definition unique_conns cs : Prop :=
  forall c0, In_active c0 cs -> unique_conn c0 cs.

Lemma In_In_active c cs :
  In c cs ->
  (has_conn_state RECVING c || has_conn_state SENDING c)%bool = true ->
  In_active c cs.
Proof.
  intros Hcs Hc.
  unfold In_active.
  apply in_or_app.
  apply has_conn_state_RS in Hc.
  destruct Hc as [Hc | Hc]; [left | right]; apply filter_In;
    (split; [ | apply has_conn_state_prop ]; auto).
Qed.

Lemma In_active_refl c cs :
  (has_conn_state RECVING c || has_conn_state SENDING c)%bool = true ->
  In_active c (c :: cs).
Proof.
  apply In_In_active.
  constructor.
  reflexivity.
Qed.

Lemma replace_In_active c cs :
  unique_conn c cs ->
  replace_active c cs = cs.
Proof.
  induction cs as [| c' cs' IH].
  - auto.
  - intros Hcs.
    simpl.
    rewrite IH.
    { destruct orb eqn:Hstate.
      + destruct eqb_connection_id.
        * { rewrite (Hcs c'); auto.
            apply In_active_refl; assumption.
          }
        * reflexivity.
      + reflexivity.
    }
    { intros c0 Hc0.
      apply Hcs.
      apply In_active_cons.
      assumption.
    }
Qed.

Lemma In_app_filter A p1 p2 (c : A) cs :
  In c (filter p1 cs ++ filter p2 cs) -> In c cs.
Proof.
  intro Hc.
  apply in_app_or in Hc.
  do 2 rewrite filter_In in Hc.
  destruct Hc as [[Hc ?]|[Hc ?]];
    assumption.
Qed.

Lemma In_active_In c cs : In_active c cs -> In c cs.
Proof.
  unfold In_active.
  apply In_app_filter.
Qed.

Lemma In_active_equiv c cs :
  In_active c cs <-> In c cs /\ is_active c.
Proof.
  unfold In_active.
  unfold is_active.
  split.
  - intro H.
    apply in_app_or in H.
    rewrite filter_In in H.
    destruct H as [[H1 H2] | H].
    + rewrite <- has_conn_state_prop in H2.
      split; auto.
    + rewrite filter_In in H.
      rewrite <- has_conn_state_prop in H.
      destruct H; split; auto.
  - intro H.
    apply in_or_app.
    destruct H as [H1 [H2 | H2]]; [left | right];
      rewrite filter_In;
      rewrite <- has_conn_state_prop;
      auto.
Qed.

Lemma In_replace_active' c c0 cs :
  In c (replace_active c0 cs) <->
  exists c',
    In c' cs /\
    c = if (has_conn_state RECVING c' || has_conn_state SENDING c')%bool
        then if (conn_id c' = conn_id c0)? then
          c0 else c'
        else c'.
Proof.
  induction cs as [ | c' cs' IH].
  - simpl; split.
    + intros [].
    + intros [? [[]]].
  - split.
    + simpl.
      intros [ Hc | Hc ].
      * exists c'.
        split; [left; reflexivity |].
        destruct orb;
          [destruct eqb_connection_id |];
          auto.
      * apply IH in Hc.
        destruct Hc as [c'' [H'' Hc'']].
        exists c''; auto.
    + intros [c1 [[Hc1 | Hc1] Hc1']].
      * left; subst; simpl.
        destruct orb; [destruct eqb_connection_id|]; reflexivity.
      * right. apply IH.
        exists c1.
        auto.
Qed.

Lemma In_replace_active c c0 cs :
  In c (replace_active c0 cs) <->
  (c = c0 /\ exists c',
      In_active c' cs /\
      conn_id c' = conn_id c0) \/
  ((conn_id c <> conn_id c0 \/ ~is_active c) /\ In c cs).
Proof.
  rewrite In_replace_active'.
  split.
  - intros [c' [H1 H2]].
    destruct orb eqn:Hstate in H2.
    destruct dec in H2.
    * left; split; auto.
      exists c'.
      split; auto.
      rewrite In_active_equiv.
      rewrite <- (has_conn_state_RS c') in Hstate.
      auto.
    * right.
      subst.
      split; [left|]; auto.
    * right.
      subst.
      split; [right| auto].
      rewrite <- (has_conn_state_DD c') in Hstate.
      intros [Hr | Hr]; destruct Hstate as [Hs | Hs];
        rewrite Hs in Hr; discriminate.
  - intros [[H0 [c' [H1 H2]]] | [H0 H1]].
    * exists c'.
      rewrite In_active_equiv in H1.
      destruct H1 as [H1 H1'].
      unfold is_active in H1'.
      rewrite has_conn_state_RS in H1'.
      rewrite H1'.
      destruct dec; try contradiction.
      auto.
    * exists c.
      split; auto.
      destruct H0 as [H0 | H0].
      { destruct orb; auto.
        destruct dec; auto.
        contradiction. }
      { unfold is_active in H0.
        rewrite has_conn_state_RS in H0.
        apply Bool.not_true_iff_false in H0.
        rewrite H0.
        reflexivity.
      }
Qed.

Lemma In_active_active :
  forall x l,
    In_active x l ->
    conn_state x = RECVING \/ conn_state x = SENDING.
Proof.
  induction l.
  - intros. apply In_active_In in H. contradiction.
  - intros. unfold In_active in H.
    apply in_app_or in H.
    destruct H;
      apply filter_In in H; destruct H;
        apply has_conn_state_prop in H0; tauto.
Qed.

Lemma In_active_inv :
  forall x h t,
    In_active x (h::t) ->
    x = h \/ In_active x t.
Proof.
  intros x h t H.
  apply In_active_In in H as H1.
  apply in_inv in H1. destruct H1.
  - intuition.
  - right. apply In_In_active.
    + assumption.
    + apply has_conn_state_RS.
      eapply In_active_active. apply H.
Qed.

Lemma unique_replace_active c0 cs :
  unique_conns cs -> unique_conns (replace_active c0 cs).
Proof.
  unfold unique_conns.
  unfold unique_conn.
  intros H c1 Hc1 c2 Hc2 Hcid.
  rewrite In_active_equiv in *.
  rewrite In_replace_active in *.
  destruct Hc1 as [Hc11 Hc12], Hc2 as [Hc21 Hc22].
  destruct Hc11 as [[Hc11 [c1' [Hc111 Hc112]]] | [Hc111 Hc112]];
    destruct Hc21 as [[Hc21 [c2' [Hc211 Hc212]]] | [Hc211 Hc212]]; subst.
  - reflexivity.
  - destruct Hc211 as [Hc211 | Hc211]; contradiction.
  - symmetry in Hcid.
    destruct Hc111 as [Hc111 | Hc111]; contradiction.
  - destruct Hc111 as [Hc111 | Hc111]; try contradiction.
    destruct Hc211 as [Hc211 | Hc211]; try contradiction.
    apply H; try rewrite In_active_equiv; auto.
Qed.

Lemma ids_replace_active c cs:
  map conn_id (replace_active c cs) = map conn_id cs.
Proof.
  induction cs; auto.
  simpl.
  destruct (has_conn_state _ _ || has_conn_state _ _)%bool;
    destruct (eqb_connection_id (conn_id a) (conn_id c)); simpl;
      f_equal; trivial.
  symmetry; trivial.
Qed.

Lemma open_network_modify_costate is_open f cid ns ns':
  open_network is_open ns ->
  (forall st, connection_status st = connection_status (f st)) ->
  ns' = Map.modify cid f ns ->
  open_network is_open ns'.
Proof.
  intros Hopen Hf Hns'; subst ns'.
  unfold open_network.
  intros c; split; [intros c_open | intros Hstatus].      
  - destruct (Hopen c) as [Hc _]; specialize (Hc c_open).
    unfold Map.modify.
    destruct (eqb_connection_id c cid) eqn:Hcid.
    + rewrite Map.update_lookup_eq; auto.
      rewrite <- Hf.
      subst; apply Hc.
    + rewrite Map.update_lookup_neq; auto.
  - destruct (Hopen c) as [_ Hc].
    apply Hc.
    revert Hstatus.
    unfold Map.modify.
    destruct (eqb_connection_id c cid) eqn:Hcid.
    + rewrite Map.update_lookup_eq; auto.
      rewrite <- Hf.
      intros; trivial.
      subst.
      destruct Hstatus; [left | right]; trivial.
    + rewrite Map.update_lookup_neq; auto.
Qed.          

Lemma is_complete_true s :
  is_complete app s = true <->
  String.length s = App.req_size app.
Proof.
  apply Nat.eqb_eq.
Qed.

Lemma is_complete_false s :
  is_complete app s = false <->
  String.length s <> App.req_size app.
Proof.
  apply Nat.eqb_neq.
Qed.

End GeneralFacts.

Section Pf.

Definition E0 := failureE +' nondetE +' serverE.

Variable ENDPOINT : endpoint_id.

(* Variable GOOD_INI : String.length INI_MSG = BUF_LEN. *)

Variable req_nonempty :
  0 < App.req_size app.

Variable resp_nonempty :
  forall req_s resp,
    resp = snd (App.app app req_s) -> 0 < String.length resp.

Definition select_loop_invariant : loop_invariant _ :=
  fun (r : state)
      (s_ : list connection * App.state app) =>
  let '(cs, app_s) := s_ in
  (forall s c, List.In c cs ->
     conn_state c = s ->
     let c' := Map.lookup (get_ns r) (conn_id c) in
     match s with
     | RECVING =>
       c' = {|
         connection_status := ACCEPTED;
         connection_inbytes := list_of_bytes (conn_request c);
         connection_outbytes := [];
       |} /\
       (String.length (conn_request c) < App.req_size app)%nat
     | SENDING =>
       c' = {|
         connection_status := ACCEPTED;
         connection_inbytes := [];
         connection_outbytes :=
           skipn (conn_response_bytes_sent c)
                 (list_of_bytes (conn_response c));
       |} /\
       conn_response_bytes_sent c < String.length (conn_response c)
     | _ => True
     end
  ) /\
  let cids := map conn_id cs in
  (forall cid, get_is_open r cid <-> List.In cid cids) /\
  get_spec r = linear_spec' app cids app_s /\
  unique_conns cs /\
  open_network_state r.

Lemma inv_open_conn r cs last_msg c :
          select_loop_invariant r (cs, last_msg) ->
          In_active c cs ->
          get_is_open r (conn_id c).
Proof.
  intros H Hactive.
  destruct H as [? [open_iff_in [? [? Hopen]]]].
  apply In_active_In in Hactive.
  rewrite open_iff_in.
  apply in_map.
  assumption.
Qed.

Theorem nrefines_recv'_ z s c k len :
  get_is_open s c ->
  open_network_state s ->
  (forall msg s',
      (String.length msg <= len)%nat ->
      s' = append_inbytes c (list_of_bytes msg) s ->
      nrefines_ z s' (k msg)) ->
  nrefines_ z s (simplify_network (Network.recv' c len) >>= k).
Proof.
  intros Hc.
  generalize dependent k.
  generalize dependent s.
  induction len; intros s Hopen k Hns Hk; simpl;
    auto_simplify_nrefines.
  - apply Hk.
    + auto.
    + unfold append_inbytes, Map.modify.
      rewrite app_nil_r.
      rewrite update_in_idem.
      erewrite Map.lookup_update_eq by reflexivity.
      { destruct s; reflexivity. }
  - apply nrefines_recv_byte_.
    { apply Hns. auto. }
    intros b s' Hs'.
    auto_simplify_nrefines.
    apply nrefines_or_; auto_simplify_nrefines.
    + apply Hk.
      { simpl.
        lia. }
      { assumption. }
    + auto_simplify_nrefines.
      apply IHlen.
      { subst s'; auto. }
      { unfold open_network_state, open_network.
        intro c0.
        subst s'.
        unfold append_inbytes.
        simpl.
        unfold Map.modify.
        destruct (eqb_connection_id c c0).
        - subst c.
          rewrite Map.update_lookup_eq by reflexivity.
          apply Hns.
        - rewrite Map.update_lookup_neq by auto.
          apply Hns.
      }
      intros msg s'' Hmsg Hs''.
      auto_simplify_nrefines.
      apply Hk.
      { simpl. lia. }
      { subst s' s''.
        unfold append_inbytes.
        unfold set_ns.
        simpl.
        rewrite Map.modify_modify_eq.
        unfold Map.modify.
        f_equal.
        unfold update_in; simpl.
        rewrite <- app_assoc.
        reflexivity. }
Qed.

Theorem nrefines_recv_ z s c k len :
  get_is_open s c ->
  open_network_state s ->
  (forall msg s',
      (String.length msg <= len)%nat ->
      s' = append_inbytes c (list_of_bytes msg) s ->
      nrefines_ z s' (k (Some msg))) ->
  nrefines_ z s (k None) ->
  nrefines_ z s (simplify_network (Network.recv c len) >>= k).
Proof.
  intros Hc Hns HkSome HkNone.
  unfold Network.recv.
  auto_simplify_nrefines.
  apply nrefines_or_; auto_simplify_nrefines.
  - assumption.
  - auto_simplify_nrefines.
    apply nrefines_recv'_; auto.
    intros msg ns' Hmsg Hns'.
    auto_simplify_nrefines.
    apply HkSome.
    { lia. }
    { assumption. }
Qed.


Theorem nrefines_send_' z s c k msg :
  get_status s c = ACCEPTED ->
  get_is_open s c ->
  List.prefix (list_of_bytes msg) (get_outbytes s c) ->
  (forall len s',
      (len <= String.length msg)%nat ->
      s' = drop_outbytes c len s ->
      nrefines_ z s' (Tau (k len))) ->
  nrefines_ z s
           (simplify_network (Network.send c msg) >>= fun _ =>
            Tau (k (String.length msg))).
Proof.
  revert k s.
  induction msg;
    intros k s Hstatus Hopen Hprefix Hk.
  { unfold Network.send.
    simpl.
    auto_simplify_nrefines.
    apply (Hk 0%nat); auto.
    simpl.
    unfold drop_outbytes.
    unfold Map.modify, update_out.
    erewrite Map.lookup_update_eq; try reflexivity.
    { destruct s; reflexivity. }
    destruct (Map.lookup (get_ns s) c); reflexivity.
  }

  unfold Network.send; simpl.
  auto_simplify_nrefines.
  apply nrefines_send_byte; [ assumption | ..].
  { simpl in Hprefix.
    destruct Hprefix as [rest Hbytes].
    simpl in Hbytes.
    rewrite Hbytes.
    unfold prefix; eexists; reflexivity.
  }

  change (for_bytes _ _) with (Network.send c msg).
  unfold drop_outbytes in *.
  remember (Map.modify c _ _) as ns'.

  simpl in IHmsg.

  apply (IHmsg (fun n => k (S n))); auto.
  - subst ns'; trivial.
    unfold Map.modify, update_out.
    unfold get_status in *.
    rewrite Hstatus. simpl.
    rewrite Map.update_lookup_eq; auto.
  - subst ns'.
    destruct Hprefix as [rest Hbytes].
    unfold get_outbytes in *.
    unfold Map.modify, update_out.
    rewrite Hbytes.
    simpl.
    rewrite Map.update_lookup_eq; auto.
    simpl.
    exists rest; auto.
  - intros len0 ns'0  Hlen' ns'0_eq.
    apply Hk.
    + simpl; omega.
    + subst ns'0; subst ns'.
      unfold set_ns; simpl.
      unfold Map.modify, update_out.
      repeat rewrite Map.update_lookup_eq; auto.
      simpl.
      rewrite Map.update_update_eq; auto.
      repeat f_equal; auto.
      destruct (connection_outbytes _); auto.
      destruct len0; auto.
Qed.

Theorem nrefines_send_ z s c (k : nat -> itree E0 unit) msg :
  get_status s c = ACCEPTED ->
  get_is_open s c ->
  List.prefix (list_of_bytes msg)
              (get_outbytes s c) ->
  (forall len s',
      (len <= String.length msg)%nat ->
      s' = drop_outbytes c len s ->
      nrefines_ z s' (k len)) ->
  nrefines_ z s (simplify_network (send_any_prefix c msg) >>= k).
Proof.
  intros Hstatus Hopen Hprefix Hk.
  unfold send_any_prefix.
  auto_simplify_nrefines.
  rewrite Stutter.simplify_choose.
  apply nrefines_choose_.
  intros x x_in.
  apply in_range in x_in.
  auto_simplify_nrefines.
  match goal with
  | |- context[fun _ : unit => ?body] =>
    replace (fun _ : unit => body)
      with (fun _ : unit => Tau (k x));
      [| replace body with (Tau (k x)); try reflexivity]
  end;
    [ | rewrite ret_bind; reflexivity ].

  replace (k x)
    with (k (String.length (substring 0 x msg)));
    [ | rewrite String.length_substring by omega; reflexivity ].

  apply nrefines_send_'; auto.

  { destruct Hprefix as [rest Hbytes].
    rewrite list_of_substring.
    simpl.
    exists (skipn x (list_of_bytes msg) ++ rest).
    rewrite Hbytes.
    rewrite app_assoc.
    rewrite firstn_skipn.
    reflexivity.
  }

  intros len ns' Hlen ns'_eq.

  apply nrefines_tau_.
  intros z' Hz'.
  apply nrefines_monotonic with (z' := z); [| omega].
  subst ns'.
  apply Hk; auto.
  rewrite String.length_substring in Hlen; [| omega].
  omega.
Qed.  

Local Definition Et := failureE +' nondetE +' observerE.

Section is_trace_lemmas.

  Import Traces.

  Lemma is_trace_weakening {A B}
        (a : A) l (k : A -> itree Et B) (tr : trace _) :
    is_trace' (choose l >>= k) tr ->
    is_trace' (choose (a :: l) >>= k) tr.
  Proof.
    intros Htr.
    rewrite bind_def.
    simpl.
    apply TraceInvis with (x:=false).
    apply Htr.
  Qed.

  Lemma is_trace_weakening2 {A B}
        (a : A) l (k : A -> itree Et B) (tr : trace _) :
    In a l ->
    is_trace' (Ret a >>= k) tr ->
    is_trace' (choose l >>= k) tr.
  Proof.
    intros. induction l.
    - contradiction.
    - simpl. apply in_inv in H.
      rewrite bind_def; simpl.
      destruct H.
      + apply TraceInvis with (x:=true).
        subst. assumption.
      + apply TraceInvis with (x:=false).
        apply IHl. assumption.
  Qed.

  Lemma obs_msg_to_server_trace cid
        k l st (dtr dtr': real_trace) :
    dtr' = to_server_trace cid st ++ dtr ->
    String.length st = l ->
    is_spec_trace (k st) dtr ->
    is_spec_trace
      (obs_msg_to_server l cid >>= k) dtr'.
  Proof.
    generalize dependent k.
    generalize dependent l.
    generalize dependent dtr.
    generalize dependent dtr'. 
    induction st.
    - intros. simpl. rewrite (match_itree (obs_msg_to_server _ _)).
      simpl in H0. subst. simpl. rewrite ret_bind. constructor. assumption.
    - intros. simpl. simpl in H0. destruct l.
      + discriminate.
      + simpl. unfold obs_to_server. simpl. unfold liftE.
        unfold is_spec_trace. rewrite H.
        repeat rewrite vis_bind. simpl.
        constructor.
        simpl in H1. inversion H0.
        rewrite bind_def; simpl.
        constructor. rewrite Eq.bind_bind.
        eapply IHst; try reflexivity.
        rewrite ret_bind. constructor. assumption.
  Qed.

  Lemma obs_msg_from_server_trace cid k st (dtr dtr' : real_trace) :
    dtr' = from_server_trace cid st ++ dtr ->
    is_spec_trace k dtr ->
    is_spec_trace (obs_msg_from_server cid st >>= fun _ => k) dtr'.
  Proof.
    generalize dependent k.
    generalize dependent dtr.
    generalize dependent dtr'. 
    induction st.
    - intros. simpl. rewrite ret_bind. constructor.
      simpl in H0. subst. assumption.
    - intros. simpl. simpl in H0. unfold obs_from_server. simpl.
      unfold liftE. rewrite Eq.bind_bind. repeat rewrite vis_bind.
      unfold is_spec_trace. rewrite H.
      unfold real_to_hypo_trace. simpl.
      constructor.
      rewrite ret_bind.
      constructor.
      simpl.
      destruct (Ascii.ascii_dec a a).
      + subst. rewrite ret_bind. rewrite tau_bind. constructor.
        eapply IHst; try reflexivity. assumption.
      + contradiction.
  Qed.
End is_trace_lemmas.

Lemma from_server_trace_transitions0 :
  forall ns p msg msg' cid,
  Map.lookup ns cid =
  {|
  connection_status := ACCEPTED;
  connection_inbytes := msg';
  connection_outbytes := p |} ->
  server_transitions (from_server_trace cid msg) ns
    (Map.modify cid
       (fun st : LinearSpec_NetworkModel.connection_state =>
        update_out (p ++ list_of_bytes msg) (update_in msg' st)) ns).
Proof.
  intros ns p msg msg' cid Hmap.
  generalize dependent ns.
  generalize dependent p.
  induction msg.
  - intros. simpl. unfold server_transitions. simpl.
    unfold update_in, update_out. simpl. rewrite app_nil_r.
    unfold Map.modify. rewrite Hmap. simpl.
    symmetry. eapply Map.lookup_update_eq; try reflexivity.
    rewrite Hmap. reflexivity.
  - intros. simpl. unfold from_server_trace. unfold server_transitions.
    simpl. eexists. split.
    + unfold server_send. rewrite Hmap. simpl. reflexivity.
    + unfold from_server_trace in IHmsg.
      unfold update_out. simpl.
      replace (Map.modify cid
                          (fun st =>
                             {|
                               connection_status := connection_status st;
                               connection_inbytes := msg';
                               connection_outbytes := p ++ a :: list_of_bytes msg |}) ns)
        with (Map.modify cid
                         (fun st =>
                            {|
                              connection_status := connection_status st;
                              connection_inbytes := msg';
                              connection_outbytes := p ++ a :: list_of_bytes msg |})
                         (Map.update cid
                                     {|
                                       connection_status := ACCEPTED;
                                       connection_inbytes := msg';
                                       connection_outbytes := p ++ [a] |} ns)).
      * unfold update_out in IHmsg; simpl in IHmsg.
        replace (p ++ a :: list_of_bytes msg)
          with ((p ++ [a]) ++ list_of_bytes msg).
        -- eapply IHmsg. apply Map.update_lookup_eq; reflexivity.
        -- rewrite <- app_assoc. reflexivity.
      * unfold Map.modify.
        rewrite Map.update_update_eq; try reflexivity. do 2 f_equal.
        rewrite Map.update_lookup_eq, Hmap; reflexivity.
Qed.

Lemma from_server_trace_transitions :
  forall ns msg msg' cid,
  Map.lookup ns cid =
  {|
  connection_status := ACCEPTED;
  connection_inbytes := msg';
  connection_outbytes := [] |} ->
  server_transitions (from_server_trace cid msg) ns
    (Map.modify cid
       (fun st : LinearSpec_NetworkModel.connection_state =>
          update_out (list_of_bytes msg) (update_in msg' st)) ns).
Proof.
  intros. replace (list_of_bytes msg) with
              ([] ++ list_of_bytes msg).
  - apply from_server_trace_transitions0. assumption.
  - reflexivity.
Qed.

Lemma to_server_trace_transitions0 :
  forall ns p msg msg' cid,
  Map.lookup ns cid =
  {|
  connection_status := ACCEPTED;
  connection_inbytes := list_of_bytes msg ++ p;
  connection_outbytes := msg' |} ->
  server_transitions (to_server_trace cid msg) ns
    (Map.modify cid
       (fun st : LinearSpec_NetworkModel.connection_state =>
          update_out msg' (update_in p st)) ns).
Proof.
  intros ns p msg msg' cid Hmap. 
  generalize dependent ns.
  generalize dependent p.
  induction msg.
  - intros. unfold server_transitions, update_in, update_out. simpl.
    unfold Map.modify. rewrite Hmap. simpl in *.
    symmetry. eapply Map.lookup_update_eq; try reflexivity.
    symmetry. apply Hmap.
  - intros. unfold to_server_trace, server_transitions. simpl.
    eexists. split.
    + unfold server_recv. rewrite Hmap. simpl.
      unfold update_in. simpl. reflexivity.
    + replace (Map.modify cid
                           (fun st =>
                              update_out msg' (update_in p st)) ns)
        with (Map.modify cid
                         (fun st =>
                            update_out msg' (update_in p st))
                         (Map.update cid
                                     {|
                                       connection_status := ACCEPTED;
                                       connection_inbytes := list_of_bytes msg ++ p;
                                       connection_outbytes := msg' |} ns)).
      * apply IHmsg. apply Map.update_lookup_eq; reflexivity.
      * unfold update_out, update_in, Map.modify. simpl.
        rewrite Map.update_update_eq; try reflexivity. do 2 f_equal.
        rewrite Map.update_lookup_eq, Hmap; reflexivity.
Qed.

Lemma to_server_trace_transitions :
  forall ns msg msg' cid,
  Map.lookup ns cid =
  {|
  connection_status := ACCEPTED;
  connection_inbytes := list_of_bytes msg;
  connection_outbytes := msg' |} ->
  server_transitions (to_server_trace cid msg) ns
    (Map.modify cid
       (fun st : LinearSpec_NetworkModel.connection_state =>
          update_out msg' (update_in [] st)) ns).
Proof.
  intros. apply to_server_trace_transitions0.
  rewrite app_nil_r. assumption.
Qed.

Lemma server_transitions_cons :
  forall p1 p2 ns1 ns2 ns3,
  server_transition p1 ns1 ns2 ->
  server_transitions p2 ns2 ns3 ->
  server_transitions (p1 :: p2) ns1 ns3.
Proof.
  intros. unfold server_transitions. simpl.
  exists ns2. intuition.
Qed.

Lemma server_transitions_cons_rev :
  forall ns1 ns2 p1 p2,
  server_transitions (p1 :: p2) ns1 ns2 ->
  exists ns', server_transition p1 ns1 ns' /\ server_transitions p2 ns' ns2.
Proof.
  intros. unfold server_transitions in H. simpl in H.
  destruct H as [ns' ?]. exists ns'. intuition.
Qed.

Lemma server_transitions_app_rev :
  forall p1 p2 ns1 ns3,
    server_transitions (p1 ++ p2) ns1 ns3 ->
    exists ns2, server_transitions p1 ns1 ns2 /\
           server_transitions p2 ns2 ns3.
Proof.
  induction p1; intros.
  - simpl in H. exists ns1. split.
    + unfold server_transitions. reflexivity.
    + assumption.
  - unfold server_transitions. simpl.
    simpl in H. apply server_transitions_cons_rev in H.
    destruct H as [ns' [Ha Hp1p2]].
    specialize (IHp1 p2 ns' ns3 Hp1p2).
    destruct IHp1 as [ns2 [Hp1 Hp2]].
    exists ns2. split; intuition.
    exists ns'. split; intuition.
Qed.
  
Lemma server_transitions_app :
  forall p1 p2 ns1 ns2 ns3,
  server_transitions p1 ns1 ns2 ->
  server_transitions p2 ns2 ns3 ->
  server_transitions (p1 ++ p2) ns1 ns3.
Proof.
  intro p1.
  apply (rev_ind (fun p1 => forall (p2 : real_trace) (ns1 ns2 ns3 : network_state),
                      server_transitions p1 ns1 ns2 ->
                      server_transitions p2 ns2 ns3 -> server_transitions (p1 ++ p2) ns1 ns3)); intros.
  - simpl. inversion H; subst. assumption.
  - rewrite <- app_assoc.
    apply server_transitions_app_rev in H0.
    destruct H0 as [ns' [Hl Hx]].
    specialize (H (x :: p2) ns1 ns' ns3 Hl). apply H.
    unfold server_transitions in Hx. simpl in Hx.
    destruct Hx as [? [? ?]]; subst.
    eapply server_transitions_cons; eassumption.
Qed.

Lemma nrefines_atomic_app_ z s t app_s app_s' req resp c cs :
  String.length req = App.req_size app ->
  (app_s', resp) = App.app app (app_s, req) ->
  let cid := conn_id c in
  In_active c cs ->
  let cids := map conn_id cs in
  ( get_spec s = linear_spec' app cids app_s /\
    Map.lookup (get_ns s) cid = {|
      connection_status := ACCEPTED;
      connection_inbytes := list_of_bytes req;
      connection_outbytes := [];
    |}
  ) ->
  let obs' := linear_spec' app cids app_s' in
  let ns' := Map.modify
               cid
               (fun st => update_out (list_of_bytes resp)
                                     (update_in [] st))
               (get_ns s) in
  let s' := set_ns ns' (set_observer obs' s) in
  nrefines_ z s' t ->
  nrefines_ z s t.

Proof.
  simpl.
  intros Hl Happ HIn [Hobs1 Hobs2] Ht.
    apply nrefines_network_transition_ with
    (dtr := to_server_trace   (conn_id c) req
         ++ from_server_trace (conn_id c) resp)
    (ns' := Map.modify
              (conn_id c)
              (fun st => update_out (list_of_bytes resp)
                                    (update_in [] st))
              (get_ns s))
    (obs' := linear_spec' app (map conn_id cs) app_s').
  - rewrite Hobs1. intros dtr Hobs'.
    rewrite (match_itree (linear_spec' app _ _)). simpl.
    apply Traces.TraceInvis with (x:=false).
    apply is_trace_weakening2 with (a:=(conn_id c)).
    + apply In_active_In in HIn. apply in_map. assumption.
    + rewrite ret_bind. constructor. rewrite <- app_assoc.
      eapply obs_msg_to_server_trace; try reflexivity. assumption.
      rewrite <- Happ.
      eapply obs_msg_from_server_trace; try reflexivity. assumption.
  - eapply server_transitions_app.
    + apply to_server_trace_transitions.
      rewrite Hobs2. reflexivity.
    + replace (Map.modify (conn_id c)
                          (fun st : LinearSpec_NetworkModel.connection_state =>
                             update_out (list_of_bytes resp) (update_in [] st)) (get_ns s))
        with (Map.modify (conn_id c)
                          (fun st : LinearSpec_NetworkModel.connection_state =>
                             update_out (list_of_bytes resp) (update_in [] st))
             (Map.modify (conn_id c)
                         (fun st : LinearSpec_NetworkModel.connection_state =>
                            update_out [] (update_in [] st)) (get_ns s))).
      * apply from_server_trace_transitions.
        unfold update_out, update_in, Map.modify. rewrite Hobs2. simpl.
        apply Map.update_lookup_eq. reflexivity.
      * unfold Map.modify. rewrite Map.update_update_eq; try reflexivity.
        unfold update_in, update_out. simpl. f_equal.
        rewrite Map.update_lookup_eq; reflexivity.
  - auto.
Qed.

Lemma nrefines_accept_connection_ z
      s ns' t msg cid cs :
  let cids := map conn_id cs in
  (get_spec s = linear_spec' app cids msg /\
   Map.lookup (get_ns s) cid = {|
     connection_status := PENDING;
     connection_inbytes := [];
     connection_outbytes := [];
   |}) ->
  let obs' := linear_spec' app (cid :: cids) msg in
  let s' := set_ns ns' (set_observer obs' s) in
  server_accept cid (get_ns s) = Some (ns', tt) ->
  nrefines_ z s' t ->
  nrefines_ z s t.

Proof.
  simpl.
  intros [Hobs1 Hobs2] Hs Ht.
  eapply nrefines_network_transition_ with
      (dtr := [NewConnection cid]); [| | eassumption].
  - rewrite Hobs1. intros dtr Hobs'.
    rewrite (match_itree (linear_spec' app _ _)). simpl.
    apply Traces.TraceInvis with (x:=true).
    unfold obs_connect. simpl. unfold liftE.
    rewrite vis_bind.
    constructor.
    rewrite ret_bind. constructor. assumption.
  - unfold server_transitions. simpl. eexists. split.
    + unfold server_accept. rewrite Hobs2. simpl. unfold accept_cs.
      simpl. reflexivity.
    + revert Hs. unfold server_accept, accept_cs. rewrite Hobs2. simpl.
      inversion 1. reflexivity.
Qed.

Lemma inv_process_recv_complete
      s s' cs cs' c app_s app_s' req resp msg :
  is_complete app req = true ->
  req = (conn_request c ++ msg)%string ->
  (app_s', resp) = App.app app (app_s, req) ->
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = RECVING ->
  get_spec s = linear_spec' app (map conn_id cs) app_s ->
  s' = set_observer
         (linear_spec' app
            (map conn_id cs)
            app_s')
         (set_ns (Map.modify (conn_id c)
                             (fun st =>
                                update_out (list_of_bytes resp)
                                           (update_in [] st))
                             (get_ns s)) s) ->
  cs' = replace_active
          {| conn_id := conn_id c;
             conn_request := req;
             conn_response := resp;
             conn_response_bytes_sent := 0;
             conn_state := SENDING |} cs ->
  select_loop_invariant s' (cs', app_s').

Proof.
  intros Hcomplete Hnew_request Happ
         [Hinv1 Hinv2] Hc HcRECVING Hobs0 Hs' Hcs'.
  split.
  { intros s0 c0 Hc0 Hc0_state c'.
    subst c' cs'.
    unfold replace_active in Hc0.
    simpl in Hc0.
    apply In_replace_when in Hc0.
    destruct Hc0 as [Hc0|[Hc0 Hc0']].
    - subst c0 s0 s'; simpl.
      unfold Map.modify.
      rewrite Map.update_lookup_eq by reflexivity.
      apply In_active_In in Hc.
      split.
      { rewrite (proj1 (Hinv1 RECVING _ Hc HcRECVING)).
        reflexivity. }
      { apply resp_nonempty with (req_s := (app_s, req)).
        rewrite <- Happ; auto. }
    - destruct orb eqn:Hstate in Hc0.
      + destruct eqb_connection_id as [Hcc0|Hcc0] in Hc0.
        * discriminate.
        * clear Hc0.
          subst s0 s'; simpl.
          unfold Map.modify.
          rewrite Map.update_lookup_neq by auto.
          apply Hinv1; auto.
      + apply has_conn_state_DD in Hstate.
        rewrite Hc0_state in Hstate.
        destruct Hstate; subst s0; exact I.
  }

  { simpl; split_and.
    - intros cid.
      subst s'; simpl.
      rewrite (proj1 Hinv2).
      match goal with
      | [ |- In _ ?x <-> In _ ?y ] => assert (He : y = x)
      end.
      { subst cs'.
        clear.
        induction cs.
        + auto.
        + simpl.
          f_equal; auto.
          destruct (orb _ _); auto.
          destruct (eqb_connection_id _ _); auto.
      }
      rewrite He.
      reflexivity.
    - subst cs'.
      unfold replace_active.
      rewrite map_replace_when.
      { subst req s'. auto. }
      { intros c' Hc'.
        destruct dec, orb in Hc'; discriminate + auto.
      }
    - subst cs'.
      apply unique_replace_active.
      apply Hinv2.
    - subst s'.
      apply In_active_In in Hc.
      apply (fun pf => pf (Hinv1 _ _ Hc HcRECVING)).
      simpl; intros [Hc_ ?].
      apply modify_open_network_open.
      + apply Hinv2.
      + apply Hinv2.
        rewrite Hc_; auto.
      + rewrite Hc_; auto.
  }
Qed.

Lemma inv_process_recv_incomplete
      s s' cs cs' c app_s new_request msg :
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = RECVING ->
  s' = append_inbytes (conn_id c) (list_of_bytes msg) s ->
  (String.length msg <=
   App.req_size app - String.length (conn_request c))%nat ->
  new_request = (conn_request c ++ msg)%string ->
  is_complete app new_request = false ->
  cs' = replace_active
          {| conn_id := conn_id c;
             conn_request := new_request;
             conn_response := conn_response c;
             conn_response_bytes_sent := conn_response_bytes_sent c;
             conn_state := RECVING |} cs ->
  select_loop_invariant s' (cs', app_s).

Proof.
  intros [Hinv1 Hinv2] Hc HcRECVING Hns' Hmsg Hnew_request Hcomplete Hcs'.
  split.
  { intros s0 c0 Hc0 Hc0_state c'.
    subst c' cs'.
    unfold replace_active in Hc0; simpl in Hc0.
    apply In_replace_when in Hc0.
    destruct Hc0 as [Hc0|[Hc0 Hc0']].
    - subst s'; simpl.
      unfold Map.modify.
      rewrite Map.update_lookup_eq by (subst c0; auto).
      simpl.
      subst c0 s0; simpl.
      apply In_active_In in Hc.
      apply (fun pf => pf (Hinv1 RECVING _ Hc HcRECVING)).
      intros [Hc' Hlen'].
      rewrite Hc'.
      split.
      * rewrite Hnew_request.
        rewrite app_list_of_bytes.
        reflexivity.
      * subst new_request.
        apply Nat.le_neq.
        split.
        { rewrite String.string_app_length.
          apply le_sub_add_le.
          - apply Nat.lt_le_incl.
            assumption.
          - assumption.
        }
        { apply is_complete_false.
          assumption.
        }

    - destruct orb eqn:Hstate in Hc0.
      + destruct eqb_connection_id in Hc0.
        * discriminate.
        * subst s'. simpl.
          unfold Map.modify.
          rewrite Map.update_lookup_neq by auto.
          apply Hinv1; auto.
      + apply has_conn_state_DD in Hstate.
        destruct Hstate as [Hstate | Hstate];
          rewrite Hstate in Hc0_state;
          subst s0;
          exact I.
  }

  { simpl; split_and.
    { intros cid.
      subst s'; simpl in *.
      rewrite (proj1 Hinv2).
      subst cs'; unfold replace_active; simpl.
      rewrite map_replace_when.
      { reflexivity. }
      { intros c'.
        destruct orb; [| discriminate].
        destruct eqb_connection_id; [| discriminate].
        intro; assumption.
      }
    }
    { subst cs' s'.
      unfold replace_active.
      rewrite map_replace_when.
      apply Hinv2.
      intros c'.
      destruct orb; [| discriminate].
      destruct dec; [| discriminate].
      intro; assumption.
    }
    { subst cs'.
      apply unique_replace_active.
      apply Hinv2. }
    { subst s'; simpl.
      apply In_active_In in Hc.
      apply (fun pf => pf (Hinv1 _ _ Hc HcRECVING)).
      simpl; intros [Hc_ ?].
      apply modify_open_network_open.
      + apply Hinv2.
      + apply Hinv2.
        rewrite Hc_; auto.
      + rewrite Hc_; auto.
    }
  }
Qed.

Lemma inv_process_recv_failed
      s cs cs' c app_s :
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = RECVING ->
  cs' = replace_active (upd_conn_state c DELETED) cs ->
  select_loop_invariant s (cs', app_s).
Proof.
  intros H Hactive Hstate cs'_eq.
  destruct H
    as [Hinvar [open_iff_in [obs_eq [Hunique_conns Hopen]]]].
  unfold select_loop_invariant.
  subst cs'.
  split; [| split; [| split; [| split]]];
    try assumption; try solve [apply unique_replace_active; assumption].
  { (* state invariant *)
    intros s0 c0 c0_in.
    unfold replace_active in c0_in.
    apply In_replace_when in c0_in.
    destruct c0_in as [c0_deleted | [c0_not_recving_sending c0_cs]].
    - rewrite <- c0_deleted; simpl.
      intros Hs; rewrite <- Hs; trivial.
    - apply Hinvar.
      trivial.
  } 
  { (* cids *)
    intros cid.
    rewrite ids_replace_active.
    trivial.
  }   
  { (* obs *)
    rewrite ids_replace_active.
    trivial.
  }   
Qed.

Lemma inv_process_send_complete
      s s' cs cs' c app_s :
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = SENDING ->
  s' = set_ns (Map.modify (conn_id c)
                          (fun st => update_out [] st)
                          (get_ns s))
              s ->
  cs' = replace_active
          {| conn_id := conn_id c;
             conn_request := "";
             conn_response := "";
             conn_response_bytes_sent := 0;
             conn_state := RECVING |} cs ->
  select_loop_invariant s' (cs', app_s).
Proof.
  intros H Hactive Hstate Hns' cs'_eq.
  destruct H
    as [Hinvar [open_iff_in [obs_eq [Hunique_conns Hopen]]]].

  unfold select_loop_invariant.
  split; [| split; [| split; [| split]]];
    try assumption; try solve [apply unique_replace_active; assumption].
  { (* state *)
    subst cs'.
    intros s0 c0 c0_in; unfold replace_active in c0_in.

    apply In_replace_when2 in c0_in.
    destruct c0_in as [[x [x_in [cond_x c0_eq]]] | [Hc0 c0_in]].
    - (* c0 freshly updated *)
      specialize (Hinvar (conn_state x) x x_in eq_refl).
      rewrite conditional_bool in cond_x.
      rewrite conditional_dec_true in cond_x.
      simpl in cond_x.
      destruct cond_x as [conn_id_xc x_state].
      rewrite conn_id_xc in *.
      simpl in Hinvar.
      assert (conn_id c0 = conn_id x) as c0_conn_id by (subst c0; auto).
      unfold unique_conns in Hunique_conns.
      unfold unique_conn in Hunique_conns.
      assert (In_active x cs) as Hactivex. {
        apply In_active_equiv.
        split; auto.
        apply has_conn_state_RS in x_state.
        unfold is_active; assumption.
      }
      specialize (Hunique_conns c Hactive x Hactivex conn_id_xc).
      subst x.
      rewrite Hstate in *.
      
      subst c0.
      simpl.
      intros Hs; rewrite <- Hs.
      subst s'.
      split; [|apply req_nonempty].
      unfold Map.modify, update_out; simpl.
      rewrite Map.update_lookup_eq; trivial.
      destruct Hinvar as [Hlookup _].
      rewrite Hlookup.
      reflexivity.
    - (* c0 not replaced *)
      rewrite <- Bool.not_true_iff_false in Hc0.
      unfold not in Hc0.
      rewrite conditional_bool in Hc0.
      rewrite conditional_dec_true in Hc0.
      rewrite <- has_conn_state_RS in Hc0.
      simpl in Hc0.
      
      specialize (Hinvar (conn_state c0) c0 c0_in eq_refl);
        simpl in Hinvar.
      intros Hs; subst s0.
      subst s'.
      unfold Map.modify, update_out.

      destruct (eqb_connection_id (conn_id c0) (conn_id c)).
      + simpl in Hc0.
        destruct (conn_state c0) eqn:Hc0_state; simpl; auto;
          exfalso; apply Hc0; tauto.
      + (* map not changed, so invariant carries over *)
        destruct (conn_state c0) eqn:Hc0_state; auto.
        * destruct Hinvar as [Hlookup ?].
          split; auto; simpl.
          rewrite <- Hlookup.
          rewrite Map.update_lookup_neq; auto.
        * destruct Hinvar as [Hlookup ?].
          split; auto; simpl.
          rewrite <- Hlookup.
          rewrite Map.update_lookup_neq; auto.
  } 
  { (* cids *)
    intros cid.
    subst cs'.
    rewrite ids_replace_active.
    subst s'; simpl.
    trivial.
  }
  { (* obs *)
    subst cs'.
    rewrite ids_replace_active.
    subst s'; simpl.
    trivial.
  }
  { (* unique_conns *)
    subst cs'.
    apply unique_replace_active.
    trivial.
  }
  {
    (* open network *)
    subst s'.
    eapply open_network_modify_costate; [| | reflexivity]; trivial.
  }     
Qed.
    
Lemma inv_process_send_incomplete
      s s' cs cs' c app_s len :
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = SENDING ->
  (len < length (get_outbytes s (conn_id c)))%nat ->
  s' = drop_outbytes (conn_id c) len s ->
  cs' = replace_active
          {| conn_id := conn_id c;
             conn_request := conn_request c;
             conn_response := conn_response c;
             conn_response_bytes_sent := conn_response_bytes_sent c + len;
             conn_state := conn_state c |} cs ->
  select_loop_invariant s' (cs', app_s).
Proof.
  intros H Hactive Hstate Hlen cs'_eq.
  destruct H
    as [Hinvar [open_iff_in [obs_eq [Hunique_conns Hopen]]]].
    
  unfold select_loop_invariant.
  split; [| split; [| split; [| split]]];
    try assumption.
  { (* state *)
    subst cs'.
    intros s0 c0 c0_in; unfold replace_active in c0_in.
    apply In_replace_when2 in c0_in.
    destruct c0_in as [[x [x_in [cond_x c0_eq]]] | [Hc0 c0_in]].
    - (* c0 freshly updated *)
      specialize (Hinvar (conn_state x) x x_in eq_refl).
      rewrite conditional_bool in cond_x.
      rewrite conditional_dec_true in cond_x.
      simpl in cond_x.
      destruct cond_x as [conn_id_xc x_state].
      rewrite conn_id_xc in *.
      simpl in Hinvar.
      assert (conn_id c0 = conn_id x) as c0_conn_id by (subst c0; auto).
      unfold unique_conns in Hunique_conns.
      unfold unique_conn in Hunique_conns.
      assert (In_active x cs) as Hactivex. {
        apply In_active_equiv.
        split; auto.
        apply has_conn_state_RS in x_state.
        unfold is_active; assumption.
      }
      specialize (Hunique_conns c Hactive x Hactivex conn_id_xc).
      subst x.
      rewrite Hstate in *.
      
      subst c0.
      simpl.
      intros Hs; rewrite <- Hs.
      subst s'; simpl in *.
      
      destruct Hinvar as [Hlookup conn_response_len].
      repeat split; [| try omega; auto..].
      2 : {
        revert Hlen.
        revert conn_response_len.
        remember (conn_response_bytes_sent c).
        unfold get_outbytes.
        rewrite Hlookup.
        unfold get_outbytes; simpl.
        rewrite skipn_length.
        rewrite length_list_of_bytes.
        remember (String.length (conn_response c)).
        clear; intros; omega.
        }

      unfold Map.modify, update_out.
      rewrite Map.update_lookup_eq; auto.
      rewrite Hlookup.
      simpl.
      f_equal.
      rewrite skipn_skipn.
      f_equal.
      omega.

    - (* c0 not replaced *)
      rewrite <- Bool.not_true_iff_false in Hc0.
      unfold not in Hc0.
      rewrite conditional_bool in Hc0.
      rewrite conditional_dec_true in Hc0.
      rewrite <- has_conn_state_RS in Hc0.
      simpl in Hc0.
      
      specialize (Hinvar (conn_state c0) c0 c0_in eq_refl);
        simpl in Hinvar.
      intros Hs; subst s0.
      subst s'.
      unfold drop_outbytes; simpl.
      unfold Map.modify, update_out.

      destruct (eqb_connection_id (conn_id c0) (conn_id c)).
      + simpl in Hc0.
        destruct (conn_state c0) eqn:Hc0_state; simpl; auto;
          exfalso; apply Hc0; tauto.
      + (* map not changed, so invariant carries over *)
        destruct (conn_state c0) eqn:Hc0_state; auto.
        * destruct Hinvar as [Hlookup ?].
          split; auto.
          rewrite <- Hlookup.
          rewrite Map.update_lookup_neq; auto.
        * destruct Hinvar as [Hlookup ?].
          split; auto.
          rewrite <- Hlookup.
          rewrite Map.update_lookup_neq; auto.
    
  } 
  { (* cids *)
    intros cid.
    subst cs'.
    rewrite ids_replace_active.
    subst s'; simpl.
    trivial.
  }
  { (* obs *)
    subst cs'.
    rewrite ids_replace_active.
    subst s'; simpl.
    trivial.
  }
  { (* unique_conns *)
    subst cs'.
    apply unique_replace_active.
    trivial.
  }
  {
    (* open network *)
    subst s'.
    eapply open_network_modify_costate; [| | reflexivity]; trivial.
  }     
Qed.
  

Lemma inv_process_send_failed
      s cs cs' c app_s :
  select_loop_invariant s (cs, app_s) ->
  In_active c cs ->
  conn_state c = SENDING ->
  cs' = replace_active (upd_conn_state c DELETED) cs ->
  select_loop_invariant s (cs', app_s).
Proof.
  intros H Hactive Hstate cs'_eq.
  destruct H
    as [Hinvar [open_iff_in [obs_eq [Hunique_conns Hopen]]]].
  unfold select_loop_invariant.
  subst cs'.
  split; [| split; [| split; [| split]]];
    try assumption; try solve [apply unique_replace_active; assumption].
  { (* state invariant *)
    intros s0 c0 c0_in.
    unfold replace_active in c0_in.
    apply In_replace_when in c0_in.
    destruct c0_in as [c0_deleted | [c0_not_recving_sending c0_cs]].
    - rewrite <- c0_deleted; simpl.
      intros Hs; rewrite <- Hs; trivial.
    - apply Hinvar.
      trivial.
  } 
  { (* cids *)
    intros cid.
    rewrite ids_replace_active.
    trivial.
  }   
  { (* obs *)
    rewrite ids_replace_active.
    trivial.
  }   
Qed.

Lemma unique_conn_unique_conns :
  forall c cs,
    unique_conns cs ->
    unique_conn c cs ->
    unique_conns (c::cs).
Proof.
  unfold unique_conns, unique_conn. intros.
  apply In_active_inv in H1; apply In_active_inv in H2.
  destruct H1; destruct H2; subst; auto.
  symmetry. apply H0; auto.
Qed.

Lemma unique_conns_unique_id :
  forall c1 c2 cs,
    unique_conns cs ->
    In_active c1 cs ->
    In_active c2 cs ->
    c1 <> c2 ->
    conn_id c1 <> conn_id c2.
Proof.
  unfold unique_conns, unique_conn. intros.
  specialize (H c1 H0 c2 H1). intro.
  symmetry in H3. apply H in H3.
  subst. contradiction.
Qed.

Lemma inv_accept s ns' ns'' c cs cs' app_s :
  let c' := {| conn_id := c;
               conn_request := ""; conn_response := "";
               conn_response_bytes_sent := 0;
               conn_state := RECVING |} in
  select_loop_invariant s (cs, app_s) ->
  client_connect c (get_ns s) = Some (ns', tt) ->
  server_accept c ns' = Some (ns'', tt) ->
  unique_conn c' cs ->
  cs' =  c' :: cs ->
  let s' := {|
        get_is_open := fun c' => c = c' \/ get_is_open s c';
        get_spec := linear_spec' app (map conn_id cs') app_s;
        get_ns := ns'' |} in
  select_loop_invariant s' (cs', app_s).
Proof.
  unfold select_loop_invariant.
  intros Hinv Hconnect Haccept Hunique Hcs'.
  repeat split.
  - intros s1 c1 HIn1 Hst1. rewrite Hcs' in HIn1.
    unfold client_connect in Hconnect.
    destruct (connection_status (Map.lookup (get_ns s) c)) eqn:Hcs; inversion Hconnect.
    rewrite <- H0 in Haccept. unfold server_accept in Haccept.
    rewrite Map.update_lookup_eq in Haccept. simpl in Haccept. inversion Haccept.
    remember {|
        conn_id := c;
        conn_request := "";
        conn_response := "";
        conn_response_bytes_sent := 0;
        conn_state := RECVING |} as c'.
    destruct (dec_eq c1 c').
    + subst s1 c1 c'. simpl. 
      rewrite Map.update_lookup_eq; try reflexivity.
      unfold pending_cs. unfold accept_cs. simpl.
      split. reflexivity. apply req_nonempty.
    + apply in_inv in HIn1 as HIn. destruct HIn as [Heq | HIn].
      * symmetry in Heq. contradiction.
      * destruct Hinv as [Hinv1 Hinv2].
        specialize (Hinv1 s1 c1 HIn Hst1).
        assert (Hneq: s1 = RECVING \/ s1 = SENDING -> conn_id c1 <> c).
        { intros. replace c with (conn_id c').
          - apply unique_conns_unique_id with (cs:=cs').
            + rewrite Hcs'. apply unique_conn_unique_conns.
              * intuition.
              * assumption.
            + apply In_In_active.
              * rewrite Hcs'. assumption.
              * apply has_conn_state_RS. subst. assumption.
            + rewrite Hcs'. apply In_In_active.
              * simpl. left. reflexivity.
              * apply has_conn_state_RS. left.
                rewrite Heqc'. reflexivity.
            + assumption.
          - subst. reflexivity. }
        destruct s1 eqn:Hs1; try reflexivity.
        -- assert (Hneq': c <> conn_id c1).
           { intro. apply Hneq; intuition. }
           simpl.
           repeat (rewrite Map.update_lookup_neq; try apply Hneq').
           intuition.
        -- assert (Hneq': c <> conn_id c1).
           { intro. apply Hneq; intuition. }
           simpl.
           repeat (rewrite Map.update_lookup_neq; try apply Hneq').
           intuition.
    + reflexivity.
  - intros Hcid. destruct Hcid as [Hcid | Hcid].
    + subst c. rewrite Hcs'. simpl. intuition.
    + destruct Hinv as [_ [Hinv _]].
      rewrite Hcs'. simpl. right. apply Hinv; assumption.
  - rewrite Hcs'. simpl. intros [Hcid | Hcid].
    + subst c. intuition.
    + right. destruct Hinv as [_ [Hinv _]]. apply Hinv; assumption.
  - rewrite Hcs'. apply unique_conn_unique_conns.
    + intuition.
    + assumption.
  - intros Hc0. unfold client_connect in Hconnect.
    destruct (connection_status (Map.lookup (get_ns s) c)) eqn:Hcs; inversion Hconnect.
    rewrite <- H0 in Haccept. unfold server_accept in Haccept.
    rewrite Map.update_lookup_eq in Haccept; try reflexivity.
    simpl in Haccept. inversion Haccept.
    destruct Hc0.
    + subst c0. simpl. rewrite Map.update_lookup_eq; try reflexivity. tauto.
    + destruct Hinv as [_ [_ [_ [_ Hinv]]]].
      unfold open_network in Hinv.
      destruct (dec_eq c c0).
      * subst c0. simpl. rewrite Map.update_lookup_eq; try reflexivity. tauto.
      * simpl.
        repeat (rewrite Map.update_lookup_neq; try assumption).
        apply Hinv; assumption.
  - unfold client_connect in Hconnect.
    simpl.
    destruct (connection_status (Map.lookup (get_ns s) c)) eqn:Hcs; inversion Hconnect.
    rewrite <- H0 in Haccept. unfold server_accept in Haccept.
    rewrite Map.update_lookup_eq in Haccept; try reflexivity.
    simpl in Haccept. inversion Haccept.
    destruct (dec_eq c c0).
    + intuition.
    + repeat (rewrite Map.update_lookup_neq; try assumption).
      intros. destruct Hinv as [_ [_ [_ [_ [_ Hinv]]]]].
      unfold open_network in Hinv. right. apply Hinv; assumption.
Qed.

Theorem nrefines_process_ z s cs app_s c k :
  select_loop_invariant s (cs, app_s) ->
  In c (filter (has_conn_state RECVING) cs ++
        filter (has_conn_state SENDING) cs) ->
  (forall s' c0 last_msg',
      (conn_id c0 = conn_id c) ->
      let cs' := replace_active c0 cs in
      select_loop_invariant s' (cs', last_msg') ->
      nrefines_ z s' (k (c0, last_msg'))) ->
  nrefines_ z s
    (simplify_network (process_conn app c app_s) >>= k).
Proof.
  intros Hinv Hc Hk.
  unfold process_conn.
  destruct (conn_state c) eqn:Hc_state.

  - (* RECVING *)
    unfold conn_read.
    auto_simplify_nrefines.
    apply nrefines_or_; auto_simplify_nrefines.

    + (* recv *)
      apply nrefines_recv_.
      { eapply inv_open_conn; eauto. }
      { apply Hinv. }
      { intros msg s' Hmsg Hs'.
        destruct is_complete eqn:Hcomplete; auto_simplify_nrefines.
        * (* Swap now *)
          destruct App.app as [app_s' resp] eqn:Happ.
          eapply nrefines_atomic_app_ with
            (cs := cs)
            (app_s := app_s)
            (app_s' := app_s')
            (req := (conn_request c ++ msg)%string)
            (resp := resp)
            (c := c).
          { apply is_complete_true; assumption. }
          { auto. }
          { auto. }
          { split.
            - subst s'. simpl. apply Hinv.
            - destruct Hinv as [Hinv ?].
              rewrite app_list_of_bytes.
              subst s'. simpl.
              unfold Map.modify.
              rewrite Map.update_lookup_eq by reflexivity.
              apply In_active_In in Hc.
              rewrite (proj1 (Hinv RECVING c Hc Hc_state)).
              reflexivity.
          }
          auto_simplify_nrefines.
          apply Hk.
          { reflexivity. }
          { eapply inv_process_recv_complete; eauto.
            - apply Hinv.
            - subst s'; simpl.
              unfold set_ns.
              simpl.
              rewrite Map.modify_modify_eq by reflexivity.
              unfold update_in; simpl.
              reflexivity.
          }
        * apply Hk.
          { auto. }
          { eapply inv_process_recv_incomplete; eauto.
          }
      }
      { auto_simplify_nrefines.
        apply Hk.
        { reflexivity. }
        { eapply inv_process_recv_failed; eauto. }
      }

    + (* recv error *)
      auto_simplify_nrefines.
      apply Hk.
      { reflexivity. }
      { rewrite replace_In_active.
        - apply Hinv.
        - apply Hinv.
          apply Hc.
      }

  - (* SENDING *)
    unfold conn_write.
    auto_simplify_nrefines.
    apply nrefines_or_; auto_simplify_nrefines.

    + (* send *)
      apply nrefines_send_.
      { unfold select_loop_invariant in Hinv.
        destruct Hinv as [Hstate_inv ?].
        specialize (Hstate_inv (conn_state c) c).
        rewrite Hc_state in Hstate_inv.
        apply In_app_filter in Hc.
        specialize (Hstate_inv Hc eq_refl).
        destruct Hstate_inv as [Hlookup ?].
        unfold get_status.
        rewrite Hlookup.
        reflexivity.
      } 
      { eapply inv_open_conn; eauto. }
      { destruct Hinv as [Hinv Hinv2].
        apply In_active_In in Hc.
        apply (fun pf => pf (Hinv SENDING _ Hc Hc_state)).
        intros [Hc' Hres].
        unfold get_outbytes.
        rewrite Hc'.
        simpl.
        rewrite list_of_substring.
        apply firstn_prefix.
      }
      intros len ns' Hlen Hns'.
      destruct Nat.ltb eqn:Hlen_.
      { rewrite Stutter.simplify_fail.
        apply nrefines_fail_. }
      clear Hlen_.
      destruct Nat.eqb eqn:Hlen_.

      * auto_simplify_nrefines.
        apply Hk.
        { reflexivity. }
        { apply inv_process_send_complete with (s := s) (cs := cs) (c := c); eauto.
          { subst ns'.
            unfold drop_outbytes; simpl.
            unfold Map.modify.
            f_equal.
            f_equal.
            destruct Hinv as [Hinv ?].
            apply In_active_In in Hc.
            apply (fun pf => pf (Hinv SENDING _ Hc Hc_state)).
            intros [Hc' Hc_len].
            rewrite Hc'.
            unfold update_out; simpl in *.
            f_equal.
            apply skipn_all.
            rewrite skipn_length.
            rewrite length_list_of_bytes.
            apply Nat.eqb_eq in Hlen_.
            { omega. }
          }
        }

      * auto_simplify_nrefines.
        apply Hk.
        { reflexivity. }
        { eapply inv_process_send_incomplete with
              (len := len); eauto.
          apply Nat.eqb_neq in Hlen_.
          destruct Hinv as [Hinv _].
          apply In_active_In in Hc.
          specialize (Hinv (conn_state c) c Hc eq_refl).
          rewrite Hc_state in Hinv.
          destruct Hinv as [Hlookup HBuf].
          unfold get_outbytes; rewrite Hlookup; simpl.
          rewrite skipn_length.
          rewrite length_list_of_bytes.

          revert Hlen.
          rewrite String.length_substring.
          - intros; omega.
          - omega.
        }

    + (* send error *)
      auto_simplify_nrefines.
      apply Hk.
      { reflexivity. }
      { eapply inv_process_send_failed; eauto. }

  - (* DONE *)
    auto_simplify_nrefines.
    apply Hk.
    { reflexivity. }
    { rewrite replace_In_active.
      - apply Hinv.
      - apply Hinv.
        apply Hc.
    }

  - (* DELETED *)
    auto_simplify_nrefines.
    apply Hk.
    { reflexivity. }
    { rewrite replace_In_active.
      - apply Hinv.
      - apply Hinv.
        apply Hc.
    }
Qed.

Theorem nrefines_server_ z :
  let s := {|
        get_is_open := fun _ => False;
        get_ns := initial_ns;
        get_spec := linear_spec app;
      |} in
  nrefines_ z s (server' app).
Proof.
  unfold server', server, server_.
  auto_simplify_nrefines.
  apply nrefines_or_.

  - (* Main branch *)
    auto_simplify_nrefines.
    rewrite Stutter.simplify_listen.
    auto_simplify_nrefines.
    unfold select_loop.
    rewrite Stutter.simplify_loop_with_state.
    rewrite Eq.loop_bind.
    apply nrefines_loop_ with (inv := select_loop_invariant).
    { simpl.
      split.
      - intros ? ? [].
      - split_and; auto.
        + reflexivity.
        + intros ? [].
        + intros c.
          split.
          * intros [].
          * intros []; discriminate.
    }
    intros z1 s1 [cs app_s] k.
    intros Hinv.
    intros Hloop.
    auto_simplify_nrefines.
    apply nrefines_or_.
    + (* accept branch *)
      unfold accept_connection.
      auto_simplify_nrefines.
      apply nrefines_or_; auto_simplify_nrefines.
      * apply nrefines_accept_.
        { apply Hinv. }
        intros c2 ns2 s2 Hc2 Hns2 Hs2.
        auto_simplify_nrefines.
        apply nrefines_or_.
        { auto_simplify_nrefines.
          unfold client_connect in Hns2.
          destruct (connection_status (Map.lookup (get_ns s1) c2)) eqn:Hns1; try discriminate.
          subst s2; simpl.
          eapply nrefines_accept_connection_ with (cid:=c2); simpl.
          { split.
            - apply Hinv.
            - inversion Hns2. rewrite Map.update_lookup_eq; reflexivity. }
          { inversion Hns2. unfold server_accept.
            rewrite Map.update_lookup_eq; reflexivity. }
          { apply Hloop.
            eapply inv_accept; eauto.
            { unfold client_connect. rewrite Hns1.  reflexivity. }
            { unfold server_accept. rewrite Map.update_lookup_eq; reflexivity. }
            { destruct Hinv as [_ [Hinv3 [_ [Hinv1 Hinv2]]]].
              specialize (Hinv3 c2). rewrite Hinv3 in Hc2.
              unfold unique_conn. simpl. intros.
              unfold open_network in Hinv2.
              apply In_active_In in H.
              apply in_map with (f:=conn_id) in H. rewrite H0 in H.
              contradiction.
            }
          }
        }
        { auto_simplify_nrefines.
          apply nrefines_shutdown_not_implemented_.
        }

      * auto_simplify_nrefines.
        apply Hloop.
        simpl; auto.

    + (* process branch *)
      auto_simplify_nrefines.
      rewrite Stutter.simplify_choose.
      apply nrefines_choose_.
      intros c Hc.
      auto_simplify_nrefines.
      apply nrefines_process_ with (cs := cs).
      { simpl; auto. }
      { auto. }
      intros s2 c2 last_msg2.
      intros Hc2 cs' Hinv2.
      auto_simplify_nrefines.
      apply Hloop.
      apply Hinv2.
  - (* Immediate exit *)
    auto_simplify_nrefines.
    apply nrefines_ret_.
Qed.

Theorem server_refines_swap :
  network_refines (server' app) (linear_spec app).
Proof.
  apply network_refines_equiv.
  apply nrefines_equiv.
  apply nrefines_server_.
Qed.

End Pf.

(* Print Assumptions server_refines_swap. **)

End LinearizationProof.

Theorem real_server_refines_swap :
  network_refines real_swap_impl' real_swap_spec.
Proof.
  apply server_refines_swap.
  admit.
  admit.
Admitted.
