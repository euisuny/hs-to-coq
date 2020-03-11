(* We generalize the refinement relation [network_refines]
   to a more compositional one [nrefines_]. *)

From Coq Require Import
     String
     ZArith
     Relations
     Wellfounded.

From Coq Require
     Setoid
     Morphisms
     Program.

From QuickChick Require Import
     Decidability.

Require Import ProofIrrelevance.

From Custom Require Import
     List
     Monad.
Import MonadNotations.
Import ListNotations.
Open Scope monad_scope.

From DeepWeb.Free.Monad
     Require Import Free Common Stutter Traces.

From DeepWeb Require Import
     Lib.NetworkAdapter
     Lib.NetworkInterface
     Lib.LinearSpec
     Lib.Util
     Spec.Swap_LinearSpec
     Spec.Swap_ImplModel.

Import SocketInterface.SocketAPI.
Import LinearSpec_Server.

Set Bullet Behavior "Strict Subproofs".

Close Scope Z_scope.

(* The state over which the network operations take place. *)

Record state := {
  get_is_open : connection_id -> Prop;
  get_ns : network_state;
  get_spec : itree specE unit;
}.

(* Some accessor functions *)

Definition set_is_open is_open s := {|
  get_is_open := is_open;
  get_ns := get_ns s;
  get_spec := get_spec s;
|}.

Definition set_ns ns s := {|
  get_is_open := get_is_open s;
  get_ns := ns;
  get_spec := get_spec s;
|}.

Definition set_observer obs s := {|
  get_is_open := get_is_open s;
  get_ns := get_ns s;
  get_spec := obs;
|}.

Definition get_status s c :=
  connection_status (Map.lookup (get_ns s) c).

Definition get_inbytes s c :=
  connection_inbytes (Map.lookup (get_ns s) c).

Definition append_inbytes c bs s :=
  set_ns (Map.modify
            c (fun st =>
                 update_in (connection_inbytes st ++ bs) st)
            (get_ns s)) s.

Definition get_outbytes s c :=
  connection_outbytes (Map.lookup (get_ns s) c).

Definition drop_outbytes c n s :=
  set_ns (Map.modify
            c
            (fun st =>
               update_out (skipn n (connection_outbytes st)) st)
            (get_ns s)) s.

Definition open_network_state s :=
  open_network (get_is_open s) (get_ns s).

Definition eq_state : state -> state -> Prop :=
  fun s s' =>
    (forall c, get_is_open s c <-> get_is_open s' c) /\
    get_ns s = get_ns s' /\
    get_spec s = get_spec s'.

Definition eq_state_refl s : eq_state s s.
Proof.
  destruct s; repeat split; auto.
Qed.

Add Parametric Relation : state eq_state
  reflexivity proved by eq_state_refl
    as eq_state_rel.

(* Step-indexed trace semantics (see also [Free.Monad.Traces])
   for the unindexed version. We add the step index to make
   reasoning about loops easier. *)

Definition size := nat.

(* A size-indexed variant of [is_trace]. *)
Inductive is_trace_ {E F : Type -> Type} {R : Type} :
  size -> itree (E +' F) R -> Traces.trace F -> Prop :=
| TraceEmpty : forall z0 s, is_trace_ z0 s []
| TraceVis : forall z z0 X (e : F X) x k tr,
    z < z0 ->
    is_trace_ z  (k x) tr ->
    is_trace_ z0 (Vis (| e) k) (Traces.Event e x :: tr)
| TraceInvis : forall z z0 X e k (x : X) tr,
    z < z0 ->
    is_trace_ z (k x) tr ->
    is_trace_ z0  (Vis (e |) k) tr
| TraceTau : forall z z0 s tr,
    z < z0 ->
    is_trace_ z  s tr ->
    is_trace_ z0 (Tau s) tr
.

Lemma is_trace_monotonic {E F R} :
  forall z z' (t : itree (E +' F) R) tr,
    z < z' ->
    is_trace_ z t tr -> is_trace_ z' t tr.
Proof.
  intros z z' t tr Hz Htr.
  generalize dependent z'.
  induction Htr; econstructor; eauto.
Qed.

Lemma is_trace_equiv {E F R} :
  forall (t : itree (E +' F) R) tr,
    is_trace' t tr <-> exists z, is_trace_ z t tr.
Proof.
  intros t tr.
  split.
  - induction 1; [ exists 0; constructor | | | ];
      (destruct IHis_trace' as [z Hz];
       exists (S z);
       econstructor;
       [unfold lt; reflexivity | apply Hz]).
  - intros [z Hz].
    induction Hz; econstructor; eauto.
Qed.

Definition is_impl_trace_ :
  size -> state -> itree implE unit -> real_trace -> Prop :=
  fun z s t tr =>
    open_trace (get_is_open s) tr /\
    is_trace_ z t (to_serverE_trace tr).

Ltac inversion_server_trace :=
  match goal with
  | [ H : is_trace_ ?z ?t (to_serverE_trace ?tr) |- _ ] =>
    let tr' := fresh tr "serverE" in
    let etr' := fresh "e" tr' in
    unfold is_impl_trace_ in *;
    remember (to_serverE_trace tr) as tr' eqn:etr';
    rewrite roundtrip_serverE_trace in etr';
    inversion H; subst
  end.

(**)

(* Generalized refinement property. *)
Definition nrefines_
           (z : size)
           (s : state)
           (impl : itree implE unit)
  := forall tr,
        is_impl_trace_ z s impl tr ->
        exists dstr : real_trace,
          network_reordered_ (get_ns s) dstr tr /\
          is_spec_trace (get_spec s) dstr.

Lemma nrefines_equiv impl spec :
  strong_network_refines impl spec <->
  forall z,
    let s := {|
          get_is_open := fun _ => False;
          get_ns := initial_ns;
          get_spec := spec;
        |} in
    nrefines_ z s impl.
Proof.
  simpl; split.
  - intros H z tr [Hopen Htr].
    apply (H tr).
    + apply equiv_open_wf; auto.
    + apply is_trace_equiv.
      eexists; eauto.
  - intros H tr Hwf Htr.
    apply is_trace_equiv in Htr.
    destruct Htr as [z Hz].
    eapply H.
    split.
    * apply equiv_open_wf; auto.
    * eassumption.
Qed.

(* Instances for rewriting *)

Import Setoid Morphisms Program.

Add Parametric Morphism E F R : (@is_trace_ E F R) with signature
  (eq ==> stutter ==> eq ==> impl) as is_trace_mor_.
Proof.
  intros z t1 t2 Ht tr Htr.
  generalize dependent t2.
  induction Htr; intros.
  - constructor.
  - inversion Ht.
    apply inj_pair2 in H2.
    apply inj_pair2 in H3.
    subst.
    econstructor. eassumption.
    auto.
  - inversion Ht.
    apply inj_pair2 in H2.
    apply inj_pair2 in H3.
    subst.
    econstructor. eassumption.
    auto.
  - inversion Ht.
    + econstructor.
      eassumption.
      auto.
    + apply (is_trace_monotonic z).
      assumption.
      auto.
Qed.

Add Parametric Morphism : is_impl_trace_ with signature
  (eq ==> eq ==> stutter ==> eq ==> impl) as is_impl_trace_mor_.
Proof.
  intros; intro HH.
  split.
  - apply HH.
  - eapply is_trace_mor_; eauto.
    apply HH.
Qed.

Add Parametric Morphism : nrefines_ with signature
  (eq ==>
   eq_state ==>
   flip stutter ==>
   impl)
  as nrefines_stutter_mor_.
Proof.
  intros until 4.
  destruct x, y0.
  unfold eq_state in H.
  unfold nrefines_ in H1.
  simpl in *.
  decompose [and] H; subst.
  apply H1; auto.
  destruct H2.
  split; eauto.
  eapply open_trace_prop; eauto.
  intro. rewrite H3. reflexivity.
  rewrite <- H0; assumption.
Qed.

Add Parametric Morphism : nrefines_ with signature
  (eq ==>
   eq_state ==>
   Eq.eq_itree ==>
   impl)
  as nrefines_eq_mor_.
Proof.
  intros. apply nrefines_stutter_mor_; auto.
  apply eq_itree_stutter.
  symmetry. assumption.
Qed.

Add Parametric Morphism :
  is_spec_trace
      with signature (Eq.eq_itree ==> eq ==> iff)
        as is_spec_trace_mor_stutter.
Proof.
  intros.
  unfold is_spec_trace.
  split; rewrite H; auto.
Qed.
