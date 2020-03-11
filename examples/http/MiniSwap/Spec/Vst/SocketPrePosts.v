Require Import DeepWeb.Lib.SocketInterface.
Require Import DeepWeb.Lib.VstLib.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Require Import DeepWeb.Free.Monad.Spec.

Require Import DeepWeb.Spec.Vst.SocketSpecs.
Require Import DeepWeb.Spec.Vst.Gprog.
Require Import DeepWeb.Spec.main.
Require Import VST.veric.compcert_rmaps.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.progs.conclib.
Require Import compcert.common.Memory.
Import MonadNotations.

Set Bullet Behavior "Strict Subproofs".

(* simplified socket specs *)
Definition recv_sig := funsig2signature ([(1%positive, tint);
   (2%positive, tptr tuchar);
   (3%positive, tuint);
   (4%positive, tint)],
   Clightdefs.tint) cc_default.

(* store a list of bytes in a CompCert memory *)
Fixpoint store_byte_list m b ofs lv :=
  match lv with
  | [] => Some m
  | v :: lv => match Mem.store Mint8unsigned m b ofs v with
               | Some m' => store_byte_list m' b (ofs + 1)%Z lv
               | None => None
               end
  end.

(* the non-step-indexed precondition for recv *)
Definition recv_pre m (k : option string -> itree socketE unit)
  client_conn buf_ptr alloc_len (z : itree socketE unit) :=
  z = (r <- recv client_conn (Z.to_nat alloc_len) ;; k r) /\
  match buf_ptr with Vptr b ofs =>
    Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + Z.max 0 alloc_len) Memtype.Cur Memtype.Writable
    | _ => False end.

(* helper functions for comparing memories *)
Definition ZMap_eq (m1 m2 : ZMap.t memval) := forall k, ZMap.get k m1 = ZMap.get k m2.
Definition PMap_eq {A} (e: A -> A -> Prop) (m1 m2 : PMap.t A) :=
    forall k, e (m1 !! k) (m2 !! k).

Fact ZMap_eq_refl : forall m, ZMap_eq m m.
Proof. unfold ZMap_eq. auto. Qed.

Hint Resolve ZMap_eq_refl.

Definition mem_ext m1 m2 :=
  PMap_eq ZMap_eq (Mem.mem_contents m1) (Mem.mem_contents m2) /\
  Mem.mem_access m1 = Mem.mem_access m2 /\ Mem.nextblock m1 = Mem.nextblock m2.

(* the non-step-indexed postcondition for recv *)
Definition recv_post m0 m r
           (k : option string -> itree socketE unit)
           buf_ptr alloc_len (z0 z : itree socketE unit) :=
  exists result contents,
    ((0 <= r <= alloc_len)%Z \/ r = SocketConstants.NO) /\
             (r > 0 -> (exists msg, result = inr (Some msg) /\
                     Zlength (val_of_string msg) = r /\
                     sublist 0 r contents = (val_of_string msg) /\
                     sublist r alloc_len contents =
                     list_repeat (Z.to_nat (alloc_len - r)) Vundef)) /\
             (r = 0 -> (result = inr None /\
                      contents = list_repeat (Z.to_nat alloc_len) Vundef)) /\
             (r < 0 -> (result = inl tt /\
                      contents = list_repeat (Z.to_nat alloc_len) Vundef))
             /\ Zlength contents = alloc_len /\
  z = match result with
                   | inl tt => z0
                   | inr msg_opt => k msg_opt
                   end /\
  match buf_ptr with Vptr b ofs =>
    exists m', store_byte_list m0 b (Ptrofs.unsigned ofs) contents = Some m' /\
        mem_ext m m'
    | _ => False end.

Definition recv_witness (r : rmap) (t : itree socketE unit) (k : option string -> itree socketE unit)
  (client_conn : connection_id) (st : SocketMap) (fd : sockfd) (buf_ptr : val) (alloc_len : Z) (sh : share) :
  ext_spec_type socket_ext_spec (EF_external "recv" recv_sig).
Proof.
  simpl.
  destruct (oi_eq_dec _ _); [discriminate|].
  destruct (oi_eq_dec _ _); [discriminate|].
  destruct (oi_eq_dec _ _); [discriminate|].
  destruct (oi_eq_dec _ _); [discriminate|].
  destruct (oi_eq_dec _ _); [|contradiction].
  split; [apply r|].
  eapply existT; [apply nil|].
  repeat (split; auto).
Defined.

(* helper lemmas about data in memory *)
Lemma memory_block_writable_perm : forall sh n b ofs r jm, writable_share sh ->
  (0 <= ofs)%Z -> (Z.of_nat n + ofs < Ptrofs.modulus)%Z ->
  app_pred (mapsto_memory_block.memory_block' sh n b ofs) r -> sepalg.join_sub r (m_phi jm) ->
  Mem.range_perm (m_dry jm) b ofs (ofs + Z.of_nat n) Memtype.Cur Memtype.Writable.
Proof.
  intros.
  rewrite mapsto_memory_block.memory_block'_eq in H2 by auto.
  unfold mapsto_memory_block.memory_block'_alt in H2.
  destruct (readable_share_dec sh).
  intros ??.
  apply VALspec_range_e with (loc := (b, ofs0)) in H2 as [? Hb]; simpl; auto.
  destruct H3 as [? J]; apply resource_at_join with (loc := (b, ofs0)) in J.
  pose proof (juicy_mem_access jm (b, ofs0)) as Hperm.
  rewrite Hb in J; inversion J; subst; simpl in *.
  - rewrite <- H8 in Hperm; simpl in Hperm.
    unfold perm_of_sh in Hperm.
    apply join_writable1 in RJ; auto.
    destruct (writable_share_dec _); [|contradiction].
    destruct (eq_dec _ _); [|apply Memory.access_perm; auto].
    eapply Mem.perm_implies; [apply Memory.access_perm; eauto | constructor].
  - rewrite <- H8 in Hperm; simpl in Hperm.
    unfold perm_of_sh in Hperm.
    apply join_writable1 in RJ; auto.
    destruct (writable_share_dec _); [|contradiction].
    destruct (eq_dec _ _); [|apply Memory.access_perm; auto].
    eapply Mem.perm_implies; [apply Memory.access_perm; eauto | constructor].
  - apply shares.writable_readable in H; contradiction.
Qed.

Lemma data_at__writable_perm : forall sh t p r jm, writable_share sh ->
  app_pred (field_at.data_at_ sh t p) r -> sepalg.join_sub r (m_phi jm) ->
  exists b ofs, p = Vptr b ofs /\
    Mem.range_perm (m_dry jm) b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof t) Memtype.Cur Memtype.Writable.
Proof.
  intros.
  rewrite data_at__memory_block in H0; destruct H0 as [[Hptr Hcompat] Hdata].
  destruct p; try contradiction.
  do 3 eexists; eauto.
  destruct Hdata as [? Hblock].
  eapply memory_block_writable_perm in Hblock; eauto;
    rewrite ?nat_of_Z_max, ?Z.max_l in * by (pose proof sizeof_pos t; omega); auto.
  { apply Ptrofs.unsigned_range. }
  { rewrite Z.add_comm; auto. }
Qed.

(* for now, SOCKAPI doesn't connect to CertiKOS *)
Axiom no_SOCKAPI : forall st, SockAPIPred.SOCKAPI st = emp.

Lemma nth_nil : forall {A} n (d : A), nth n nil d = d.
Proof.
  destruct n; auto.
Qed.

Lemma ghost_join_nth : forall (a b c : ghost) n, join a b c ->
  join (nth n a None) (nth n b None) (nth n c None).
Proof.
  intros; revert n; induction H; intro; rewrite ?nth_nil; try constructor.
  destruct n; eauto.
Qed.

Lemma has_ext_join : forall {Z} phi1 phi2 phi3 (z1 z2 : Z) (Hext : nth O (ghost_of phi1) None = Some (ext_ghost z1, NoneP))
  (Hj : join phi1 phi2 phi3) (Hrest : joins (ghost_of phi3) [Some (ext_ref z2, NoneP)]),
  z1 = z2 /\ nth O (ghost_of phi3) None = Some (ext_ghost z1, NoneP).
Proof.
  simpl; intros.
  apply ghost_of_join, ghost_join_nth with (n := O) in Hj.
  rewrite Hext in Hj.
  destruct Hrest as [? Hrest].
  apply ghost_join_nth with (n := O) in Hrest.
  inv Hj.
  - split; auto.
    rewrite <- H2 in Hrest; inv Hrest.
    destruct a3; inv H4; simpl in *.
    inv H; repeat inj_pair_tac.
    destruct c0; inv H8; simpl in *.
    inv H4.
    destruct g as [[]|]; try contradiction.
    inv H.
    destruct vc as (? & [[]|] & vc); hnf in vc; try congruence.
    clear - vc; destruct vc as (? & ? & ?%join_Tsh & ?); tauto.
  - rewrite <- H1 in Hrest; inv Hrest.
    destruct a3, a4; inv H5; simpl in *.
    inv H3.
    destruct a2; inv H2; simpl in *.
    inv H3; inj_pair_tac.
    inv H; repeat inj_pair_tac.
    destruct b0, c0; inv H9; simpl in *.
    destruct c1; inv H8; simpl in *.
    destruct g as [[]|], g0 as [[]|]; try contradiction.
    { destruct H as (? & ? & ?%join_Tsh & ?); tauto. }
    inv H.
    inv H6; [|inv H8].
    assert (o = None) by (inv H2; auto); subst.
    destruct o1 as [[]|]; inv H3.
    split.
    + destruct vc0 as (? & [[]|] & vc0); hnf in vc0; try congruence.
      clear - vc0; destruct vc0 as (? & ? & ?%join_Tsh & ?); tauto.
    + unfold ext_ghost; simpl; repeat f_equal; apply proof_irr.
Qed.

Lemma has_ext_eq : forall {Z} (z : Z) phi, app_pred (has_ext z) phi ->
  ghost_of phi = [Some (ext_ghost z, NoneP)].
Proof.
  intros ??? (? & _ & ->); simpl.
  unfold ext_ghost; simpl; repeat f_equal.
  apply proof_irr.
Qed.

(* first part of connection: if the VST precondition holds on a state,
    then the simplified precondition also holds *)
Lemma recv_pre_simp : forall (r : rmap) k conn st fd buf_ptr alloc_len sh ge tys args z jm
  (Hpre : ext_spec_pre (JE_spec _ socket_ext_spec) (EF_external "recv" recv_sig)
    (recv_witness r z k conn st fd buf_ptr alloc_len sh) ge tys args z jm)
  (Hext : joins (ghost_of (m_phi jm)) [Some (ext_ref z, NoneP)]),
  recv_pre (m_dry jm) k conn buf_ptr alloc_len z.
Proof.
  intros.
  hnf in Hpre.
  unfold recv_witness in Hpre.
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  destruct (oi_eq_dec _ _); [|contradiction].
  destruct Hpre as (_ & phi0 & phi1 & J & Hpre & Hr); simpl in Hpre.
  rewrite no_SOCKAPI in Hpre.
  unfold SEPx in Hpre; simpl in Hpre.
  rewrite sepcon_emp, emp_sepcon in Hpre.
  destruct Hpre as ((_ & _ & _ & Hwritable & _) & _ & ? & ? & J1 & Htrace & Hbuf); simpl in *.
  split.
  - clear - J J1 Htrace Hext.
    destruct Htrace as (t' & ? & Htrace).
    apply has_ext_eq in Htrace.
    eapply join_sub_joins_trans in Hext; [|eexists; apply ghost_of_join; eauto].
    eapply has_ext_join in Hext as []; eauto.
    rewrite Htrace; auto.
    admit. (* trace inclusion *)
  - clear - J J1 Hr Hwritable Hbuf.
    destruct (data_at__writable_perm _ _ _ _ jm Hwritable Hbuf) as (? & ? & ? & Hperm); subst; simpl.
    { eapply sepalg.join_sub_trans; [|eexists; eauto].
      eexists; eauto. }
    simpl in Hperm.
    rewrite Z.mul_1_l in Hperm; auto.
Admitted.

Lemma store_byte_list_access : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  Memory.access_at m = Memory.access_at m'.
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    rewrite (Memory.store_access _ _ _ _ _ _ Hstore); eauto.
Qed.

Lemma store_byte_list_nextblock : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    etransitivity; [|eapply Mem.nextblock_store; eauto]; eauto.
Qed.

Lemma store_byte_list_contents : forall m b ofs v m',
  store_byte_list m b ofs v = Some m' ->
  forall b' ofs',
    (b=b' /\ ofs <= ofs' < ofs + Zlength v) \/
     contents_at m (b', ofs') = contents_at m' (b', ofs').
Proof.
  intros until v; revert m ofs; induction v; simpl; intros.
  - inv H; auto.
  - destruct (Mem.store _ _ _ _ _) eqn: Hstore; [|discriminate].
    rewrite Zlength_cons.
    destruct (IHv _ _ _ H b' ofs') as [(? & ? & ?) | <-];
      [left; split; auto; split; auto; omega|].
    destruct (eq_block b b').
    subst b'.
    assert (ofs <= ofs' < ofs + Z.succ (Zlength v) \/
      (ofs' < ofs \/ ofs' >= ofs + Z.succ (Zlength v))) as [? | ?] by omega; auto.
    right.
    unfold contents_at; rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore); simpl.
    rewrite PMap.gss.
    rewrite Mem.setN_other; auto.
    intro; rewrite encode_val_length; simpl.
    pose proof Zlength_nonneg v; omega.
    { right.
      unfold contents_at; rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore); simpl.
      rewrite PMap.gso by auto. auto. }
Qed.

Lemma store_byte_list_contents' : forall jm b ofs v m' loc' rsh sh mv,
  store_byte_list (m_dry jm) b ofs v = Some m' ->
  ~ adr_range (b, ofs) (Zlength v) loc'
  -> (m_phi jm) @ loc' = YES rsh sh (VAL mv) NoneP -> contents_at m' loc' = mv.
Proof.
destruct jm. simpl.
intros.
destruct loc' as (b', ofs').
destruct (store_byte_list_contents _ _ _ _ _ H b' ofs') as [|<-]; [contradiction|].
eapply JMcontents; eauto.
Qed.

Definition store_byte_list_juicy_mem jm m' b ofs v
  (Hstore : store_byte_list (m_dry jm) b ofs v = Some m') : juicy_mem.
Proof.
 refine (mkJuicyMem m' (inflate_store m' (m_phi jm)) _ _ _ _).
(* contents_cohere *)
intros rsh sh' v' loc' pp H2.
unfold inflate_store in H2; rewrite resource_at_make_rmap in H2.
destruct (m_phi jm @ loc'); try destruct k; try solve [inversion H2].
inversion H2; auto.
(* access_cohere *)
intro loc; generalize (juicy_mem_access jm loc); intro H0.
unfold inflate_store; rewrite resource_at_make_rmap.
rewrite <- (store_byte_list_access _ _ _ _ _ Hstore).
destruct (m_phi jm @ loc); try destruct k; auto.
(* max_access_cohere *)
intro loc; generalize (juicy_mem_max_access jm loc); intro H1.
unfold inflate_store; rewrite resource_at_make_rmap.
unfold max_access_at in *.
rewrite <- (store_byte_list_access _ _ _ _ _ Hstore).
apply store_byte_list_nextblock in Hstore.
destruct (m_phi jm @ loc); auto.
destruct k; simpl; try assumption.
(* alloc_cohere *)
hnf; intros.
unfold inflate_store. rewrite resource_at_make_rmap.
generalize (juicy_mem_alloc_cohere jm loc); intro.
rewrite (store_byte_list_nextblock _ _ _ _ _ Hstore) in H.
rewrite (H0 H). auto.
Defined.

Definition mem_ext_juicy jm m' (H : mem_ext m' (m_dry jm)) : juicy_mem.
Proof.
  refine (mkJuicyMem m' (m_phi jm) _ _ _ _); repeat intro;
    destruct H as (Hcontents & Haccess & Hnextblock); destruct jm; simpl in *.
  - unfold contents_at.
    unfold PMap_eq in Hcontents.
    rewrite Hcontents; eapply JMcontents; eauto.
  - unfold access_at.
    rewrite Haccess; apply JMaccess.
  - unfold max_access_at, access_at.
    rewrite Haccess; apply JMmax_access.
  - rewrite Hnextblock in *; apply JMalloc; auto.
Defined.

Lemma data_at__store_join : forall sh z jm b ofs v m' phi0 phi1 phi2 phi3
  (Hsh : writable_share sh) (Hdata : app_pred (data_at_ sh (tarray tuchar z) (Vptr b ofs)) phi0)
  (Hz : Zlength v <= Z.max 0 z) (Hstore : store_byte_list (m_dry jm) b (Ptrofs.unsigned ofs) v = Some m')
  (Hphi0 : join_sub phi0 phi1) (Hj : join phi1 phi2 phi3) (Hjm : join_sub phi3 (m_phi jm)),
  join (inflate_store m' phi1) phi2 (inflate_store m' phi3).
Proof.
  intros.
  destruct (join_level _ _ _ Hj) as [Hl1 Hl2].
  apply resource_at_join2; unfold inflate_store; rewrite ?level_make_rmap, ?resource_at_make_rmap, ?ghost_of_make_rmap; auto.
  intro; apply resource_at_join with (loc := loc) in Hj.
  destruct (adr_range_dec (b, Ptrofs.unsigned ofs) (Zlength v) loc).
  - destruct loc as (b', ofs'); destruct a; subst.
    rewrite data_at__memory_block in Hdata; destruct Hdata as ([_ Hcompat] & _ & Hdata).
    assert (Z.of_nat (nat_of_Z (sizeof (tarray tuchar z))) = Z.max 0 z) as Heq.
    { rewrite nat_of_Z_max; simpl.
      pose proof Zlength_nonneg v.
      rewrite Z.max_l; omega. }
    rewrite mapsto_memory_block.memory_block'_eq in Hdata.
    unfold mapsto_memory_block.memory_block'_alt in Hdata.
    destruct (readable_share_dec sh).
    apply VALspec_range_e with (loc := (b', ofs')) in Hdata.
    assert (exists sh' rsh' v, writable_share sh' /\ phi1 @ (b', ofs') = YES sh' rsh' (VAL v) NoneP)
      as (? & ? & ? & Hsh' & HYES).
    { apply resource_at_join_sub with (l := (b', ofs')) in Hphi0 as [? Hphi0].
      destruct Hdata as [[] HYES]; rewrite HYES in *.
      inv Hphi0; do 4 eexists; try reflexivity; eapply join_writable1; eauto. }
    rewrite HYES in *.
    destruct (YES_join_full _ _ _ _ _ _ Hj Hsh') as (? & ? & HNO); rewrite HNO in *.
    inv Hj; constructor; auto.
    + split; auto.
      rewrite Heq; omega.
    + contradiction n; apply shares.writable_readable; auto.
    + apply Ptrofs.unsigned_range.
    + rewrite Heq; simpl in *; omega.
  - destruct (phi3 @ loc) eqn: H3; try solve [inv Hj; constructor; auto].
    rewrite <- (resource_at_approx phi2 loc), Hl1, Hl2.
    destruct k; try solve [inv Hj; constructor; auto].
    assert (exists sh' r', m_phi jm @ loc = YES sh' r' (VAL m) p) as (? & ? & H3').
    { apply resource_at_join_sub with (l := loc) in Hjm as [? Hjm].
      rewrite H3 in Hjm; inv Hjm; eauto. }
    destruct (juicy_mem_contents jm _ _ _ _ _ H3'); subst.
    eapply store_byte_list_contents' with (loc' := loc) in Hstore; eauto.
    rewrite Hstore; inv Hj; constructor; auto.
  - apply ghost_of_join; auto.
Qed.

Definition set_ghost (jm : juicy_mem) (g : ghost) :
  {jm' : juicy_mem | jm_update jm jm' /\ ghost_of (m_phi jm') = own.ghost_approx jm g}.
Proof.
  destruct (make_rmap (resource_at (m_phi jm)) (own.ghost_approx jm g) (level jm))
    as (r' & ? & Hr & ?).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  unshelve eexists (mkJuicyMem (m_dry jm) r' _ _ _ _).
  { repeat intro; rewrite Hr in *; eapply juicy_mem_contents; eauto. }
  { repeat intro; rewrite Hr in *; eapply juicy_mem_access; eauto. }
  { repeat intro; rewrite Hr in *; eapply juicy_mem_max_access; eauto. }
  { repeat intro; rewrite Hr in *; eapply juicy_mem_alloc_cohere; eauto. }
  repeat split; auto.
Defined.

Lemma store_bytes_data_at: forall sh alloc_len contents b o jm m x' phid phi0' phi1
  (Hbuf : app_pred (data_at_ sh (tarray tuchar alloc_len) (Vptr b o)) phid)
  (Hstore : store_byte_list (m_dry jm) b (Ptrofs.unsigned o) contents = Some m)
  (J' : join x' phid phi0') (J'' : join phi0' phi1 (m_phi jm)),
app_pred (data_at sh (tarray tuchar alloc_len) contents (Vptr b o)) (inflate_store m phid).
Proof.
Admitted.

Lemma join_ext_gen : forall {Z} (z z' : Z) g,
  join (Some (ext_ghost z, NoneP)) g (Some (ext_ghost z, NoneP)) ->
  join (Some (ext_ghost z', NoneP)) g (Some (ext_ghost z', NoneP)).
Proof.
  intros; inv H; [constructor|].
  destruct a2; inv H3; simpl in *.
  inv H0; inv H; repeat inj_pair_tac.
  destruct b0; inv H4; simpl in *.
  assert (o = None) by (inv H0; auto); subst.
  destruct g as [[]|]; [|repeat constructor].
  destruct H as (? & ? & ?%join_Tsh & ?); tauto.
Qed.

(* second part of connection: if the simplified postcondition holds on a state,
    then the VST postcondition also holds *)
Lemma recv_post_simp : forall jm0 r m res k conn st fd buf_ptr alloc_len sh ge tys args z0 z
  (Hpre : ext_spec_pre (JE_spec _ socket_ext_spec) (EF_external "recv" recv_sig)
    (recv_witness r z0 k conn st fd buf_ptr alloc_len sh) ge tys args z0 jm0)
  (Hext : joins (ghost_of (m_phi jm0)) [Some (ext_ref z0, NoneP)])
  (Hpost : recv_post (m_dry jm0) m res k buf_ptr alloc_len z0 z),
  exists jm, m_dry jm = m /\
  ext_spec_post (JE_spec _ socket_ext_spec) (EF_external "recv" recv_sig)
    (recv_witness r z0 k conn st fd buf_ptr alloc_len sh) ge (Some AST.Tint) (Some (Vint (Int.repr res))) z jm.
Proof.
  intros.
  unfold recv_witness in *; hnf in Hpre; simpl.
  unfold funspec2post; simpl.
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  unfold funspec2post; simpl.
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  unfold funspec2post; simpl.
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  unfold funspec2post; simpl.
  destruct (oi_eq_dec _ _); [discriminate | clear n; hnf in Hpre].
  unfold funspec2post; simpl.
  destruct (oi_eq_dec _ _); [|contradiction].
  destruct Hpre as (_ & phi0 & phi1 & J & Hpre & Hr); simpl in Hpre.
  rewrite no_SOCKAPI in Hpre.
  unfold SEPx in Hpre; simpl in Hpre.
  rewrite sepcon_emp, emp_sepcon in Hpre.
  destruct Hpre as ((_ & _ & _ & Hwritable & _) & _ & phix & phid & J1 & Htrace & Hbuf).
  destruct Hpost as (result & contents & Hres & Hrp & Hr0 & Hrn & Hlen & Hz & Hstore).
  destruct buf_ptr; try contradiction; simpl in *.
  
  destruct (set_ghost jm0 (Some (ext_ghost (match result with
         | (tt|) => z0
         | (|msg_opt) => k msg_opt
         end), NoneP) :: tl (ghost_of (m_phi jm0)))) as (jm & (Hdry & Hl & Hjm) & Hg).
  replace (ghost_fmap _ _ _) with (Some (ext_ghost (match result with
         | (tt|) => z0
         | (|msg_opt) => k msg_opt
         end), NoneP) :: tl (ghost_of (m_phi jm0))) in Hg
    by (rewrite <- ghost_of_approx at 1; destruct (ghost_of (m_phi jm0)); auto).
  rewrite <- Hdry in Hstore.
  destruct Hstore as (m' & Hstore & Hm').
  exists (mem_ext_juicy (store_byte_list_juicy_mem _ _ _ _ _ Hstore) m Hm'); split; auto.
  destruct (make_rmap (resource_at phi0) (Some (ext_ghost (match result with
         | (tt|) => z0
         | (|msg_opt) => k msg_opt
         end), NoneP) :: tl (ghost_of phi0)) (level phi0)) as (phi0' & Hl' & Hr' & Hg').
  { extensionality; apply resource_at_approx. }
  { simpl; f_equal.
    rewrite <- ghost_of_approx at 2.
    destruct (ghost_of phi0); auto. }
  destruct (make_rmap (resource_at phix) [Some (ext_ghost (match result with
         | (tt|) => z0
         | (|msg_opt) => k msg_opt
         end), NoneP)] (level phix)) as (x' & Hlx' & Hrx' & Hgx'); auto.
  { extensionality; apply resource_at_approx. }
  destruct Htrace as (? & ? & Htrace).
  pose proof (has_ext_eq _ _ Htrace) as Hgx.
  assert (joins (ghost_of phi0) [Some (ext_ref z0, NoneP)]) as Hext'.
  { eapply join_sub_joins_trans; eauto; eexists; apply ghost_of_join; eauto. }
  eapply has_ext_join in Hext' as [_ Hg0]; eauto; [|rewrite Hgx; simpl; eauto].
  assert (join x' phid phi0') as J'.
  { destruct (join_level _ _ _ J1).
    apply resource_at_join2; try omega.
    { intro; rewrite Hrx', Hr'; apply resource_at_join; auto. }
    rewrite Hgx', Hg'.
    apply ghost_of_join in J1; rewrite Hgx in J1; inv J1; constructor; auto.
    rewrite <- H5 in Hg0; simpl in Hg0; subst.
    eapply join_ext_gen; eauto. }
  assert (join phi0' phi1 (m_phi jm)) as J''.
  { eapply has_ext_join in Hext as [_ Hg1]; eauto.
    destruct (join_level _ _ _ J).
    rewrite !level_juice_level_phi in Hl.
    apply resource_at_join2; try omega.
    { intro; rewrite Hr', Hjm; apply resource_at_join; auto. }
    rewrite Hg', Hg.
    apply ghost_of_join in J.
    inv J; simpl.
    { rewrite <- H3 in Hg0; discriminate. }
    { rewrite H5; constructor. }
    constructor; auto.
    rewrite <- H2 in Hg0; simpl in Hg0; subst.
    rewrite <- H4 in Hg1; simpl in Hg1; subst.
    eapply join_ext_gen; eauto. }
  exists (inflate_store m' phi0'), phi1; split.
  { eapply data_at__store_join; eauto.
    - rewrite Hlen.
      apply Z.le_max_r.
    - eexists; eauto.
    - apply join_sub_refl. }
  split; auto.
  exists result, st, res, contents.
  split.
  { split; auto.
    split; split; auto; split; auto; try tauto.
    - split; [tauto|].
       admit. (* SockAPI *)
    - split; [tauto|].
       split; auto.
      admit. (* SockAPI *) }
  split.
  { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
  rewrite no_SOCKAPI; unfold SEPx; simpl.
  rewrite sepcon_emp, emp_sepcon.
  exists x', (inflate_store m' phid); split; [|split].
  - eapply join_comm, data_at__store_join; eauto.
    + rewrite Hlen.
        apply Z.le_max_r.
    + apply join_sub_refl.
    + eexists; eauto.
  - simpl.
    eexists; split; [apply Traces.trace_incl_refl|].
    destruct Htrace as (P & ? & _); exists P; simpl.
    rewrite Hrx', Hgx'; split; auto.
    unfold ext_ghost; simpl; repeat f_equal; apply proof_irr.
  - eapply store_bytes_data_at; eauto.
Admitted.
