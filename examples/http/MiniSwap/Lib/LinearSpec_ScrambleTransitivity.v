Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.LinearSpec_NetworkModel
     Lib.LinearSpec_Traces
     Lib.LinearSpec_Scramble.

Set Bullet Behavior "Strict Subproofs".

Module TransitivityProof <: ScrambleTransitivityType.

Fixpoint Exists {A} (P : A -> Prop) (xs : list A) : Prop :=
  match xs with
  | [] => False
  | [x] => P x
  | x :: xs => P x \/ Exists P xs
  end.

Definition combined_networks (ns01 ns12 ns02 : network_state) : Prop :=
  forall c,
    let cs01 := Map.lookup ns01 c in
    let cs12 := Map.lookup ns12 c in
    let cs02 := Map.lookup ns02 c in
    ( Exists
        (fun '(a, b, c) => connection_status cs01 = a /\
                                 connection_status cs12 = b /\
                                 connection_status cs02 = c)
        [ (CLOSED  , CLOSED  , CLOSED  );
          (CLOSED  , PENDING , PENDING );
          (PENDING , ACCEPTED, PENDING );
          (ACCEPTED, ACCEPTED, ACCEPTED) ]
    ) /\
    ( connection_inbytes cs02
      =
      connection_inbytes cs01 ++ connection_inbytes cs12
    ) /\
    ( connection_outbytes cs02
      =
      connection_outbytes cs12 ++ connection_outbytes cs01
    ).

Definition valid_state (ns : network_state) : Prop :=
  forall c,
    let cs := Map.lookup ns c in
    ( connection_status cs = CLOSED /\
      connection_outbytes cs = [] /\
      connection_inbytes cs = []
    ) \/
    ( connection_status cs = PENDING /\
      connection_outbytes cs = []
    ) \/
    ( connection_status cs = ACCEPTED ).

Ltac forget0 f ns :=
  let fd := fresh ns "field" in
  let e := fresh ns "e" in
  try (remember (f (_ ns _)) as fd eqn:e; clear e).

Ltac forget1 ns :=
  forget0 connection_status ns;
  forget0 connection_inbytes ns;
  forget0 connection_outbytes ns.

Ltac forgets nss :=
  lazymatch nss with
  | (?nss', ?ns) => forget1 ns; forgets nss'
  | ?ns => forget1 ns
  end.

Ltac decomposes Hs :=
  lazymatch Hs with
  | (?Hs, ?H) =>
    decompose [Logic.or and] H; clear H;
    (* try (subst; discriminate); *)
    decomposes Hs
  | ?H => decompose [Logic.or and] H
  end.

Ltac decomposes' Hs :=
  lazymatch Hs with
  | (?Hs, ?H) =>
    progress decompose [Logic.or and] H; clear H;
    try (subst; discriminate);
    decomposes' Hs
  | ?H => progress decompose [Logic.or and] H
  end.

Ltac compare_conns c c0 :=
  destruct (eqb_connection_id c c0);
  [ subst c0;
    repeat rewrite Map.update_lookup_eq by reflexivity
  | repeat rewrite Map.update_lookup_neq by assumption
  ].

Ltac auto_valid_state :=
  match goal with
  | [ |- valid_state ?ns' ] =>
    match ns' with
    | Map.update ?c ?s ?ns =>
      let c0 := fresh "c0" in
      intro c0; simpl;
      compare_conns c c0;
       [
       | match goal with
         | [ H : valid_state ns |- _ ] => apply H
         end
       ]
    | ?ns' =>
      match goal with
      | [ H : ns' = _ |- _ ] => rewrite H; auto_valid_state
      end
    end
  end.

Lemma reordered_transitive_empty
      (ns12 ns02 ns01 : network_state) tr2 :
  valid_state ns12 ->
  valid_state ns02 ->
  valid_state ns01 ->
  combined_networks ns01 ns12 ns02 ->
  network_reordered_ ns12 [] tr2 ->
  network_reordered_ ns02 [] tr2.
Proof.
  intros H12 H02 H01 Hns H2.
  generalize dependent Hns.
  generalize dependent ns02.
  remember [] as tr1 in H2.
  induction H2; intros ns02 H02 Hns.
  - constructor.
  - discriminate.
  - destruct e eqn:Hev.

    + (* Connect *)
      simpl in H.
      apply client_connect_success in H.
      destruct H as [Hstatus Hns'].
      apply ScrambleClient with
        (ns' := Map.update c pending_cs ns02).
      { simpl.
        apply client_connect_success.
        split; [| reflexivity].
        specialize (Hns c).
        simpl in Hns.
        forgets (ns01, ns02, ns).
        subst;
          intuition discriminate.
      }
      apply IHnetwork_reordered_; auto.
      { auto_valid_state; [ simpl; tauto ]. }
      { auto_valid_state; [ simpl; tauto ]. }
      { intro c0.
        subst ns'.
        destruct (Hns c0) as [Hns0 [Hns1 Hns2]].
        compare_conns c c0.
        - specialize (H01 c). specialize (H02 c). simpl in *.
          forgets (ns01, ns02, ns).
          decomposes (Hns0, H01, H02);
          try match goal with
              | [ H : _ ++ _ = [] |- _ ] =>
                apply app_eq_nil in H; destruct H
              end;
          subst; try discriminate; intuition.
        - auto.
      }

    + (* Client send *)
      simpl in H.
      apply client_send_success in H.
      destruct H as [Hstatus Hns'].
      apply ScrambleClient with
        (ns' := Map.modify
                  c
                  (fun cs => update_in (connection_inbytes cs ++ [b]) cs) ns02).
      { simpl.
        apply client_send_success.
        split; [reflexivity | ].
        specialize (Hns c).
        simpl in Hns.
        forgets (ns01, ns02, ns).
        decomposes Hns;
          subst;
          try discriminate;
          tauto.
      }
      unfold Map.modify in *.
      apply IHnetwork_reordered_; auto.
      { auto_valid_state.
        specialize (H12 c).
        simpl in *.
        forgets ns.
        intuition.
      }
      { auto_valid_state.
        specialize (H02 c).
        specialize (Hns c).
        simpl in *.
        forgets (ns, ns02).
        intuition (subst; discriminate).
      }
      { intro c0.
        subst ns'.
        clear H2 Hns'.
        destruct (Hns c0) as [Hns0 [Hns1 Hns2]].
        compare_conns c c0.
        - simpl in *.
          forgets (ns01, ns, ns02).
          intuition; rewrite app_assoc; subst; auto.
        - auto.
      }

    + (* Client recv *)
      simpl in H.
      apply client_recv_success in H.
      destruct H as [Hns' [Hstatus Hb]].
      apply ScrambleClient with
        (ns' := Map.modify
                  c
                  (fun cs => update_out (tl (connection_outbytes cs)) cs) ns02).
      { simpl.
        apply client_recv_success.
        unfold Map.modify.
        rewrite Map.update_lookup_eq by auto.
        split; [reflexivity |].
        specialize (Hns c). specialize (H02 c). simpl in *.
        forgets (ns01, ns, ns02).
        intuition (subst; auto; try discriminate).
      }
      unfold Map.modify in *.
      apply IHnetwork_reordered_; auto.
      { auto_valid_state. auto. }
      { auto_valid_state. simpl.
        specialize (H02 c).
        specialize (Hns c).
        simpl in *.
        forgets (ns, ns01, ns02).
        intuition (subst; discriminate).
      }
      { intro c0.
        rewrite Hns'.
        destruct (Hns c0) as [Hns0 [Hns1 Hns2]].
        compare_conns c c0; [ | auto ].
        specialize (H01 c). specialize (H02 c). simpl in *.
        forgets (ns01, ns02, ns).
        intuition (subst; auto; try discriminate).
      }
Qed.

Lemma server_transition_valid e ns ns' :
  server_transition e ns ns' ->
  valid_state ns -> valid_state ns'.
Proof.
  intros He Hns c0.
  destruct e as [ c | c b | c b ];
    simpl in He;
    [ rewrite server_accept_success in He
    | rewrite server_recv_success in He
    | rewrite server_send_success in He
    ]; simpl in He; decompose [Logic.or and] He; clear He;
      match goal with [ H : ns' = _ |- _ ] => rewrite H end;
      unfold Map.modify;
      compare_conns c c0;
      auto.
Qed.

Lemma client_transition_valid e ns ns' :
  client_transition e ns ns' ->
  valid_state ns -> valid_state ns'.
Proof.
  intros He Hns c0.
  specialize (Hns c0); simpl in Hns.
  destruct e as [ c | c b | c b ];
    simpl in He;
    [ rewrite client_connect_success in He
    | rewrite client_send_success in He
    | rewrite client_recv_success in He
    ]; simpl in He; decompose [Logic.or and] He; clear He;
      match goal with [ H : ns' = _ |- _ ] => rewrite H end;
      unfold Map.modify;
      compare_conns c c0;
      auto; intuition.
Qed.

Lemma reordered_transitive_ ns01 ns12 ns02 tr0 tr1 tr2 :
  valid_state ns01 ->
  valid_state ns12 ->
  valid_state ns02 ->
  combined_networks ns01 ns12 ns02 ->
  network_reordered_ ns01 tr0 tr1 ->
  network_reordered_ ns12 tr1 tr2 ->
  network_reordered_ ns02 tr0 tr2.

Proof.
  intros Hns01 Hns12 Hns02 Hcombined H01_reordered H12_reordered.
  generalize dependent tr2.
  generalize dependent Hcombined.
  generalize dependent Hns02.
  generalize dependent Hns12.
  generalize dependent Hns01.
  generalize dependent ns02.
  generalize dependent ns12.

  induction H01_reordered as
    [ ns01
    | ns01 ns01' ? ? ? ? H01_reordered IH
    | ns01 ns01' ? ? ? ? H01_reordered IH ];
    intros.
  { (* ScrambleEmpty *)
    apply reordered_transitive_empty with
      (ns01 := ns01) (ns12 := ns12); auto.
  }

  { (* ScrambleServer *)
    assert (He : exists ns02',
               server_transition e ns02 ns02' /\
               combined_networks ns01' ns12 ns02').
    { destruct e eqn:Hev; simpl in *.
      - (* Accept *)
        apply server_accept_success in H.
        destruct H as [Hstatus Hns'].
        eexists; rewrite server_accept_success.
        split; [split; [ |eauto ] |].
        { specialize (Hcombined c); simpl in Hcombined.
          forgets (ns01, ns02).
          intuition (subst; discriminate).
        }
        intro c0.
        rewrite Hns'.
        unfold Map.modify.

        compare_conns c c0.
        + specialize (Hcombined c).
          specialize (Hns01 c).
          specialize (Hns02 c).
          simpl in *.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; try discriminate).

        + clear dependent c.
          specialize (Hcombined c0).
          simpl in *.
          forgets (ns01, ns12, ns02).
          tauto.

      - (* Recv *)
        rewrite server_recv_success in H.
        destruct H as [Hns' [Hstatus Hbs]].
        exists (Map.modify c (update_in (connection_inbytes (Map.lookup ns01' c) ++ connection_inbytes (Map.lookup ns12 c))) ns02).
        rewrite server_recv_success; simpl.
        unfold Map.modify.
        rewrite Map.update_lookup_eq by auto; simpl.
        split.
        { split; auto.
          specialize (Hcombined c); simpl in Hcombined.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; try discriminate).
        }
        intro c0.
        rewrite Hns'.
        unfold Map.modify.

        compare_conns c c0.
        + specialize (Hcombined c).
          specialize (Hns01 c).
          simpl in *.
          tauto.
        + specialize (Hcombined c0).
          simpl in *.
          tauto.

      - (* Send *)
        rewrite server_send_success in H.
        destruct H as [Hns' Hstatus].
        exists (Map.modify c (fun cs => update_out (connection_outbytes cs ++ [b]) cs) ns02).
        rewrite server_send_success; simpl.
        split; [split; auto |].
        { specialize (Hcombined c); simpl in Hcombined.
          forgets (ns01, ns02, ns12).
          intuition (subst; discriminate).
        }
        intro c0.
        subst ns01'.
        unfold Map.modify.

        compare_conns c c0.
        + specialize (Hcombined c).
          specialize (Hns01 c).
          specialize (Hns02 c).
          simpl in *.
          forgets (ns01, ns02, ns12).
          intuition (subst; try discriminate).
          rewrite app_assoc; auto.

        + specialize (Hcombined c0); simpl in *.
          forgets (ns01, ns12, ns02).
          tauto.
    }
    destruct He as [ns02' [Hns02' Hcombined']].
    apply ScrambleServer with (ns' := ns02'); auto.
    apply IH with (ns12 := ns12) (ns02 := ns02'); auto.
    eapply server_transition_valid; eauto.
    eapply server_transition_valid; eauto.
  }

  { (* ScrambleClient *)
    remember (e :: tr_client) as tr1.
    generalize dependent ns02.
    induction H12_reordered as
        [ ns12
        | ns12 ns12' e' tr' ? ? H12_reordered IH2
        | ns12 ns12' e' tr' ? ? H12_reordered IH2 ];
      intros.

    - (* ScrambleEmpty *) discriminate.

    - (* ScrambleServer *)
      inversion Heqtr1; subst; clear Heqtr1.
      apply IH with
        (ns12 := ns12'); auto.
      + eapply client_transition_valid; eauto.
      + eapply server_transition_valid; eauto.

      + intro c0.
        specialize (Hcombined c0).
        specialize (Hns01 c0).
        specialize (Hns12 c0).
        clear IH IH2 H01_reordered H12_reordered Hns02.
        simpl in *.
        destruct e eqn:Hev; simpl in *;
          [ rewrite client_connect_success in H
          ; rewrite server_accept_success in H0
          | rewrite client_send_success in H
          ; rewrite server_recv_success in H0
          | rewrite client_recv_success in H
          ; rewrite server_send_success in H0
          ]; simpl in *;
          decompose [Logic.or and] H;
          decompose [Logic.or and] H0;
          let rewr v :=
              try match goal with
                  | [ H : v = _ |- _ ] =>
                    let X := fresh "X" in
                    let eX := fresh "eX" in
                    remember v as X eqn:eX;
                    rewrite eX in H at 1;
                    rewrite eX;
                    repeat rewrite H;
                    subst X
                  end in
          rewr ns01'; rewr ns12';
          unfold Map.modify;
          compare_conns c c0; simpl in *;
            forgets (ns01, ns12, ns02);
          decompose [Logic.or and] Hcombined; clear Hcombined;
            subst; try discriminate;
          decompose [Logic.or and] Hns01; clear Hns01;
            subst; try discriminate;
          decompose [Logic.or and] Hns12; clear Hns12;
            subst; try discriminate;
            intuition;
            try (rewrite <- app_assoc; auto).

    - (* ScrambleClient *)
      assert (He : exists ns02',
                 client_transition e' ns02 ns02' /\
                 combined_networks ns01 ns12' ns02').
    { destruct e' eqn:Hev; simpl in *.
      - (* Connect *)
        apply client_connect_success in H0.
        destruct H0 as [Hstatus Hns'].
        eexists; rewrite client_connect_success.
        split; [split; [ |eauto ] |].
        { specialize (Hcombined c); simpl in Hcombined.
          forgets (ns01, ns02, ns12).
          intuition (subst; discriminate).
        }
        intro c0.
        rewrite Hns'.

        compare_conns c c0.
        + specialize (Hcombined c).
          specialize (Hns12 c).
          specialize (Hns02 c).
          simpl in *.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; discriminate).
        + specialize (Hcombined c0).
          simpl in *.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; discriminate).

      - (* Send *)
        rewrite client_send_success in H0.
        destruct H0 as [Hns' Hstatus].
        exists (Map.modify c (fun cs => update_in (connection_inbytes cs ++ [b]) cs) ns02).
        rewrite client_send_success; simpl.
        split; [split; auto |].
        { specialize (Hcombined c); simpl in Hcombined.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; discriminate).
        }
        intro c0.
        subst ns12'.
        unfold Map.modify.

        specialize (Hcombined c0).
        compare_conns c c0;
          simpl in *;
          forgets (ns01, ns12, ns02);
          intuition (subst; try discriminate; rewrite app_assoc; auto).

      - (* Recv *)
        rewrite client_recv_success in H0.
        destruct H0 as [Hns' [Hstatus Hbs]].
        exists (Map.modify c (update_out (connection_outbytes (Map.lookup ns12' c) ++ connection_outbytes (Map.lookup ns01 c))) ns02).
        rewrite client_recv_success; simpl.
        unfold Map.modify.
        rewrite Map.update_lookup_eq by auto; simpl.
        split.
        { specialize (Hcombined c).
          specialize (Hns02 c). simpl in *.
          forgets (ns01, ns12, ns02).
          intuition (subst; auto; try discriminate).
        }
        intro c0.
        rewrite Hns'.
        unfold Map.modify.

        compare_conns c c0.
        + specialize (Hcombined c).
          simpl in *.
          forgets (ns01, ns12, ns02).
          intuition (subst; try discriminate).
        + specialize (Hcombined c0).
          simpl in *.
          forgets (ns01, ns12, ns02).
          intuition.
    }

    destruct He as [ns02' [Hns02' Hcombined']].
    apply ScrambleClient with (ns' := ns02'); auto.
    apply IH2; auto.
    eapply client_transition_valid; eauto.
    eapply client_transition_valid; eauto.
  }
Qed.

Lemma initial_valid : valid_state initial_ns.
Proof. intro; auto. Qed.

Lemma initial_combined :
  combined_networks initial_ns initial_ns initial_ns.
Proof. intro; simpl; auto. Qed.

Global Instance reordered_transitive : Transitive network_reordered.
Proof.
  unfold Transitive.
  intros a b c.
  apply reordered_transitive_;
    apply initial_valid + apply initial_combined.
Qed.

End TransitivityProof.
