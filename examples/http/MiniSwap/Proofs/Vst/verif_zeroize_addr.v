From Custom Require Import String.

Require Import DeepWeb.Spec.ServerDefs.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog zeroize_addr_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib.

Set Bullet Behavior "Strict Subproofs".

Lemma mapsto_zero_tuchar_join_tushort sh p:
  readable_share sh ->
  field_compatible tushort [] p ->
  mapsto sh tuchar p (Vint Int.zero) * mapsto sh tuchar (offset_val 1 p) (Vint Int.zero) |--
  mapsto sh tushort p (Vint Int.zero).
Proof.
  intros Hsh Hcompat.
  inversion Hcompat.
  simpl in H0.
  destruct H0 as [_  [Hsize_compat [Halign _]]].
  entailer!.
  
  unfold mapsto; simpl.
  destruct p; simpl; try solve [rewrite sepcon_FF; auto].
  rewrite !if_true by auto.

  rewrite distrib_orp_sepcon.
  apply orp_left; Intros.
  rewrite distrib_orp_sepcon2.
  apply orp_left; Intros.
  apply orp_right1; entailer!.
  
  match goal with
  | |- ?P1 * ?P2 |-- ?Q =>
    change (predicates_hered.derives (P1 * P2) Q)
  end.

  unfold predicates_hered.derives.
  intros rmap.
  intros [rmap0 [rmap1 [J01 [app_pred0 app_pred1]]]].
  destruct app_pred0
    as [v0 [[[v0_len [v0_val v0_aligned]] rest0] noghost0]].
  destruct app_pred1
    as [v1 [[[v1_len [v1_val v1_aligned]] rest1] noghost1]].

  destruct v0 as [| v0 nil0]; try discriminate.
  destruct nil0; try discriminate.
  destruct v1 as [| v1 nil1]; try discriminate.
  destruct nil1; try discriminate.

  simpl.

  unfold decode_val in v0_val, v1_val; simpl in v0_val, v1_val.
  destruct v0 as [| b0 |]; try discriminate.
  destruct v1 as [| b1 |]; try discriminate.

  assert (b0 = Byte.zero /\ b1 = Byte.zero) as [b0_zero b1_zero].
  {
    unfold decode_int in *; simpl in *.
    unfold rev_if_be in *; simpl in *.
    Transparent Archi.big_endian.
    unfold Archi.big_endian in *; simpl in *.
    Opaque Archi.big_endian.
    rewrite Z.add_0_r in *.
    split; apply initialize.zero_ext_inj; congruence.
  }

  exists [Byte Byte.zero; Byte Byte.zero].

  repeat split.
  { (* alignment *)
    inversion Halign.
    simpl in H3.
    inversion H3; subst ch.
    simpl in H4.
    assumption.
  }

  { (* share *)

    intro addr; specialize (rest0 addr); specialize (rest1 addr).
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J01.
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 1) in * by computable.
    
    assert (0 <= Ptrofs.unsigned i + 1 <= Ptrofs.max_unsigned).
    {
      revert Hsize_compat.
      unfold size_compatible.
      simpl.
      intros; split; rep_omega.
    }
    subst b0 b1.
      
    rewrite Ptrofs.unsigned_repr in * by auto.
    destruct addr; simpl in rest0, rest1.

    if_tac in rest0; if_tac in rest1; unfold adr_range in *.
    -
      (* contradiction *)
      omega.
      
    - (* ptr *)
      rewrite if_true by (repeat split; try tauto; omega).
      destruct rest0 as [rsh Heq].
      exists rsh.
      pose proof (rest1 _ _ (sepalg.join_comm J01)) as rmap_eq.
      rewrite <- rmap_eq.
      rewrite Heq.
      simpl.
      replace (z - Ptrofs.unsigned i) with 0 by omega; auto.

    - (* ptr + 1 *)

      rewrite if_true by (repeat split; try tauto; omega).
      destruct rest1 as [rsh Heq].
      exists rsh.
      rewrite <- (rest0 _ _ J01), Heq; simpl.
      replace (z - (Ptrofs.unsigned i + 1)) with 0 by omega.
      replace (z - Ptrofs.unsigned i) with 1 by omega; auto.

    - (* outside [ptr, ptr + 1] *)
      
      assert (~(b = b0 /\ Ptrofs.unsigned i <= z < Ptrofs.unsigned i + 2)).
      {
        unfold not; intros [? [z_lower z_upper]]; subst.
        apply Classical_Prop.not_and_or in H4;
          apply Classical_Prop.not_and_or in H5.
        destruct H4, H5; try contradiction.
        omega.
      } 
      rewrite if_false by assumption.
      rewrite <- (rest0 _ _ J01); auto.
  } 

  { (* ghost *)
    apply compcert_rmaps.RML.ghost_of_join in J01.
    rewrite <- (noghost0 _ _ J01); auto.
  } 

Qed.

Lemma mapsto_zero_tuchar_join_tuint sh p:
  readable_share sh ->
  field_compatible tuint [] p ->
  mapsto sh tuchar p (Vint Int.zero) *
  mapsto sh tuchar (offset_val 1 p) (Vint Int.zero) *
  mapsto sh tuchar (offset_val 2 p) (Vint Int.zero) *
  mapsto sh tuchar (offset_val 3 p) (Vint Int.zero)
         |--
         mapsto sh tuint p (Vint Int.zero).
Proof.
  intros Hsh Hcompat.
  inversion Hcompat.
  simpl in H0.
  destruct H0 as [_  [Hsize_compat [Halign _]]].
  entailer!.
  
  unfold mapsto; simpl.
  destruct p; simpl; try solve [rewrite sepcon_FF; auto].
  rewrite !if_true by auto.

  repeat rewrite sepcon_assoc.
  repeat rewrite guarded_sepcon_orp_distr; [| intros; discriminate ..].

  apply orp_left; Intros.
  apply orp_right1.

  repeat rewrite <- sepcon_assoc.

  match goal with
  | |- ?P1 * ?P2 * ?P3 * ?P4 |-- ?Q =>
    change (predicates_hered.derives (P1 * P2 * P3 * P4) Q)
  end.

  unfold predicates_hered.derives.
  intros rmap.

  intros Hpred_app.
  pose proof Hpred_app as Hpred_app'.
  
  (* Destruct *)
  destruct Hpred_app' as [rmap012 [rmap3 [J0123 app_pred]]].
  destruct app_pred
    as [app_pred012 app_pred3].
  destruct app_pred012
    as [rmap01 [rmap2 [J012 [app_pred01 app_pred2]]]].
  destruct app_pred01
    as [rmap0 [rmap1 [J01 [app_pred0 app_pred1]]]].

  destruct app_pred3
    as [v3 [[[v3_len [v3_val v3_aligned]] rest3] noghost3]].
  destruct app_pred2
    as [v2 [[[v2_len [v2_val v2_aligned]] rest2] noghost2]].
  destruct app_pred1
    as [v1 [[[v1_len [v1_val v1_aligned]] rest1] noghost1]].
  destruct app_pred0
    as [v0 [[[v0_len [v0_val v0_aligned]] rest0] noghost0]].

  destruct v3 as [| v3 r]; try discriminate;
    destruct r; try discriminate.
  destruct v2 as [| v2 r]; try discriminate;
    destruct r; try discriminate.
  destruct v1 as [| v1 r]; try discriminate;
    destruct r; try discriminate.
  destruct v0 as [| v0 r]; try discriminate;
    destruct r; try discriminate.
  
  unfold decode_val in *; simpl  in v0_val, v1_val, v2_val, v3_val.
  destruct v0 as [| b0 |], v1 as [| b1 |], v2 as [| b2 |], v3 as [| b3 |];
    try discriminate.

  assert (b0 = Byte.zero /\ b1 = Byte.zero /\ b2 = Byte.zero /\ b3 = Byte.zero)
    as [b0_zero [b1_zero [b2_zero b3_zero]]].
  {
    unfold decode_int in *; simpl in *.
    unfold rev_if_be in *; simpl in *.
    Transparent Archi.big_endian.
    unfold Archi.big_endian in *; simpl in *.
    Opaque Archi.big_endian.
    rewrite Z.add_0_r in *.
    repeat split; apply initialize.zero_ext_inj; congruence.
  }
  subst b0 b1 b2 b3.
  
  (* Destruct again *)
  
  match goal with
  | [H: predicates_hered.app_pred (?P1 * ?P2 * ?P3 * ?P4) _ |- _] =>
    replace (P1 * P2 * P3 * P4)
      with (P3 * P4 * P1 * P2) in H by
        (rewrite sepcon_assoc;
         rewrite sepcon_comm;
         rewrite <- sepcon_assoc;
         reflexivity)
  end.

  destruct Hpred_app as [rmap231 [rmap1' [J2301 app_pred]]].
  destruct app_pred
    as [app_pred230 app_pred1].
  destruct app_pred230
    as [rmap23 [rmap0' [J230 [app_pred23 app_pred0]]]].
  destruct app_pred23
    as [rmap2' [rmap3' [J23 [app_pred2 app_pred3]]]].

  destruct app_pred3
    as [v3' [[[v3_len' [v3_val' v3_aligned']] rest3'] noghost3']].
  destruct app_pred2
    as [v2' [[[v2_len' [v2_val' v2_aligned']] rest2'] noghost2']].
  destruct app_pred1
    as [v1' [[[v1_len' [v1_val' v1_aligned']] rest1'] noghost1']].
  destruct app_pred0
    as [v0' [[[v0_len' [v0_val' v0_aligned']] rest0'] noghost0']].

  destruct v3' as [| v3' r]; try discriminate;
    destruct r; try discriminate.
  destruct v2' as [| v2' r]; try discriminate;
    destruct r; try discriminate.
  destruct v1' as [| v1' r]; try discriminate;
    destruct r; try discriminate.
  destruct v0' as [| v0' r]; try discriminate;
    destruct r; try discriminate.

  unfold decode_val in *; simpl  in v0_val', v1_val', v2_val', v3_val'.
  destruct v0' as [| b0' |], v1' as [| b1' |], v2' as [| b2' |], v3' as [| b3' |];
    try discriminate.
  
  simpl.
  
  assert (b0' = Byte.zero /\ b1' = Byte.zero /\ b2' = Byte.zero /\ b3' = Byte.zero)
    as [b0_zero [b1_zero [b2_zero b3_zero]]].
  {
    unfold decode_int in *; simpl in *.
    unfold rev_if_be in *; simpl in *.
    Transparent Archi.big_endian.
    unfold Archi.big_endian in *; simpl in *.
    Opaque Archi.big_endian.
    rewrite Z.add_0_r in *.
    repeat split; apply initialize.zero_ext_inj; congruence.
  }

  subst b0' b1' b2' b3'.
  
  exists [Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero].
  
  repeat split.
  { (* alignment *)
    inversion Halign.
    simpl in H5.
    inversion H5; subst ch.
    simpl in H6.
    assumption.
  }

  { (* share *)

    intro addr;
      specialize (rest0 addr); specialize (rest1 addr);
        specialize (rest2 addr); specialize (rest3 addr);
          specialize (rest0' addr); specialize (rest1' addr);
            specialize (rest2' addr); specialize (rest3' addr).
      
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J01.
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J012.
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J0123.

    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J2301.
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J230.
    apply (compcert_rmaps.RML.resource_at_join _ _ _ addr) in J23.
    
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 1),
    (Ptrofs.unsigned_repr 2), (Ptrofs.unsigned_repr 3)
      in * by computable.
    
    assert (0 <= Ptrofs.unsigned i + 3 <= Ptrofs.max_unsigned).
    {
      revert Hsize_compat.
      unfold size_compatible.
      simpl.
      intros; split; rep_omega.
    }

    assert (0 <= Ptrofs.unsigned i + 2 <= Ptrofs.max_unsigned).
    {
      revert Hsize_compat.
      unfold size_compatible.
      simpl.
      intros; split; rep_omega.
    }

    assert (0 <= Ptrofs.unsigned i + 1 <= Ptrofs.max_unsigned).
    {
      revert Hsize_compat.
      unfold size_compatible.
      simpl.
      intros; split; rep_omega.
    }
    
    rewrite Ptrofs.unsigned_repr in * by auto.

    destruct addr; simpl in rest0, rest1, rest2, rest3.

    if_tac in rest0; if_tac in rest1; if_tac in rest2; if_tac in rest3;
      unfold adr_range in *; try omega;
        try rewrite Ptrofs.unsigned_repr in * by omega.

    - (* z = ptr *)
      match goal with
      | [H: b = b0 /\ _ |- _] =>
        destruct H as [? z_range];
          subst
      end.
      
      simpl.
      
      if_tac; unfold adr_range in *.
      2: {
        exfalso.
        match goal with
        | [H: ~(_ /\ _ <= z < Ptrofs.unsigned i + 4) |- _] => 
          apply H; split; auto; omega
        end.
      }

      destruct rest0 as [rsh Heq].
      exists rsh.
      
      replace (z - Ptrofs.unsigned i) with 0 in * by omega.
      simpl in Heq; simpl.
      unfold sepalg.identity in *.
      specialize (rest1 _ _ (sepalg.join_comm J01)).
      specialize (rest2 _ _ (sepalg.join_comm J012)).
      specialize (rest3 _ _ (sepalg.join_comm J0123)).

      rewrite <- Heq.
      rewrite rest1.
      rewrite rest2.
      rewrite rest3.

      reflexivity.

    - (* z = ptr + 1 *)

      match goal with
      | [H: b = b0 /\ _ |- _] =>
        destruct H as [? z_range];
          subst
      end.
      
      simpl.

      if_tac; unfold adr_range in *.
      2: {
        exfalso.
        match goal with
        | [H: ~(_ /\ _ <= z < Ptrofs.unsigned i + 4) |- _] => 
          apply H; split; auto; omega
        end.
      }

      destruct rest1 as [rsh Heq].
      exists rsh.

      replace (z - Ptrofs.unsigned i) with 1 in * by omega.
      replace (z - (Ptrofs.unsigned i + 1)) with 0 in * by omega.      
      simpl in Heq; simpl.
      
      specialize (rest0 _ _ J01).
      specialize (rest2 _ _ (sepalg.join_comm J012)).
      specialize (rest3 _ _ (sepalg.join_comm J0123)).
      rewrite <- Heq, rest0, rest2, rest3.
      
      reflexivity.

    - (* z = ptr + 2 *)
            
      match goal with
      | [H: b = b0 /\ _ |- _] =>
        destruct H as [? z_range];
          subst
      end.

      simpl in rest0', rest1', rest2', rest3'.

      destruct (adr_range_dec (b0, Ptrofs.unsigned i) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].
      
      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 1) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].

      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 3) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].
      
      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 2) 1 (b0, z));
        unfold adr_range in *.

      2: {
        apply Classical_Prop.not_and_or in n.
        destruct n; contradiction.
      } 
      
      if_tac; unfold adr_range in *.
      2: {
        exfalso.
        match goal with
        | [H: ~(_ /\ _ <= z < Ptrofs.unsigned i + 4) |- _] => 
          apply H; split; auto; omega
        end.
      }

      destruct rest2' as [rsh Heq].
      exists rsh.

      simpl.
      
      replace (z - Ptrofs.unsigned i) with 2 in * by omega.
      replace (z - (Ptrofs.unsigned i + 2)) with 0 in * by omega.
      simpl in Heq; simpl.

      unfold sepalg.identity in rest3'.
      specialize (rest3' _ _ (sepalg.join_comm J23)).
      specialize (rest1' _ _ (sepalg.join_comm J2301)).
      specialize (rest0' _ _ (sepalg.join_comm J230)).      
      rewrite <- Heq.
      rewrite rest3'.
      rewrite rest0'.
      rewrite rest1'.
      reflexivity.

    - (* z = ptr + 3 *)

      match goal with
      | [H: b = b0 /\ _ |- _] =>
        destruct H as [? z_range];
          subst
      end.

      simpl in rest0', rest1', rest2', rest3'.

      destruct (adr_range_dec (b0, Ptrofs.unsigned i) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].
      
      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 1) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].
      
      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 2) 1 (b0, z));
        unfold adr_range in *; [omega | clear n].

      destruct (adr_range_dec (b0, Ptrofs.unsigned i + 3) 1 (b0, z));
        unfold adr_range in *.

      2: {
        apply Classical_Prop.not_and_or in n.
        destruct n; contradiction.
      } 
      
      if_tac; unfold adr_range in *.
      2: {
        exfalso.
        match goal with
        | [H: ~(_ /\ _ <= z < Ptrofs.unsigned i + 4) |- _] => 
          apply H; split; auto; omega
        end.
      }

      destruct rest3' as [rsh Heq].
      exists rsh.

      simpl.
      
      replace (z - Ptrofs.unsigned i) with 3 in * by omega.
      replace (z - (Ptrofs.unsigned i + 3)) with 0 in * by omega.
      simpl in Heq; simpl.

      unfold sepalg.identity in rest2'.
      specialize (rest2' _ _ J23).
      specialize (rest1' _ _ (sepalg.join_comm J2301)).
      specialize (rest0' _ _ (sepalg.join_comm J230)).      
      rewrite <- Heq.
      rewrite rest2'.
      rewrite rest0'.
      rewrite rest1'.
      reflexivity.

    - (* outside *)
      assert (~(b = b0 /\ Ptrofs.unsigned i <= z < Ptrofs.unsigned i + 4)).
      {
        unfold not; intros [? [z_lower z_upper]]; subst.
        apply Classical_Prop.not_and_or in H11;
          apply Classical_Prop.not_and_or in H10;          
          apply Classical_Prop.not_and_or in H9;
          apply Classical_Prop.not_and_or in H8.
        destruct H8, H9, H10, H11; try contradiction.
        omega.
      } 
      rewrite if_false by assumption.
      rewrite <- (rest3 _ _ (sepalg.join_comm J0123)).
      rewrite <- (rest2 _ _ (sepalg.join_comm J012)).
      rewrite <- (rest1 _ _ (sepalg.join_comm J01)).
      assumption.
  }     

  { (* ghost *)
    apply compcert_rmaps.RML.ghost_of_join in J01.
    apply compcert_rmaps.RML.ghost_of_join in J012.
    apply compcert_rmaps.RML.ghost_of_join in J0123.
    
    rewrite <- (noghost3 _ _ (sepalg.join_comm J0123)).
    rewrite <- (noghost2 _ _ (sepalg.join_comm J012)).
    rewrite <- (noghost1 _ _ (sepalg.join_comm J01)).
    assumption.
  } 

Qed.

  
Lemma sockaddr_struct: forall ptr,
  field_compatible (Tstruct _sockaddr_in noattr) [] ptr ->
  data_at Tsh (tarray tuchar 16)
  [Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
  Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
  Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
  Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
  Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
  Vint (Int.repr 0)] ptr |--
  data_at Tsh (Tstruct _sockaddr_in noattr)
      (Vint (Int.repr 0),
      (Vint (Int.repr 0),
      (Vint (Int.repr 0),
      [Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
      Vint (Int.repr 0); Vint (Int.repr 0); Vint (Int.repr 0); 
      Vint (Int.repr 0); Vint (Int.repr 0)]))) ptr.
Proof.
  intro.
  unfold data_at at 2.
  unfold field_at.
  unfold at_offset.
  entailer!.

  simpl.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  repeat rewrite <- sepcon_assoc.
  
  assert (field_compatible0 (Tarray tuchar 16 noattr) [ArraySubsc 8] ptr)
    as Hcompat_sin_zero_arr.
  { apply field_compatible_field_compatible0.
    pose proof
         (field_compatible_cons (Tarray tuchar 16 noattr)
                                (ArraySubsc 8) [] ptr) as Harr.
    simpl in Harr.
    destruct Harr as [_ Harr].
    apply Harr.
    split; auto.
    omega.
  }
  
  assert (field_compatible0 (Tarray tuchar 8 noattr) [ArraySubsc 4] ptr)
    as Hcompat_sin_addr_arr.
  {
    apply field_compatible_field_compatible0.
    pose proof
         (field_compatible_cons (Tarray tuchar 8 noattr)
                                (ArraySubsc 4) [] ptr) as Harr.
    simpl in Harr.
    destruct Harr as [_ Harr].
    apply Harr.
    split; [omega |].
    apply field_compatible_array_smaller0 with (n' := 16); auto.
    omega.
  }
  
  assert (field_compatible0 (Tarray tuchar 4 noattr) [ArraySubsc 2] ptr)
    as Hcompat_sin_port_arr.
  { apply field_compatible_field_compatible0.
    pose proof
         (field_compatible_cons (Tarray tuchar 4 noattr)
                                (ArraySubsc 2) [] ptr) as Harr.
    simpl in Harr.
    destruct Harr as [_ Harr].
    apply Harr.
    split; [omega |].
    apply field_compatible_array_smaller0 with (n' := 16); auto.
    omega.
  }
  
  unfold tarray;
    rewrite split2_data_at_Tarray_tuchar with (n1 := 8) by (auto; omega).
  unfold field_address0; simpl.
  rewrite if_true; [| assumption].
  unfold sublist; simpl.
  unfold data_at at 2, field_at, at_offset; Intros.
  simpl.
  entailer!.

  rewrite split2_data_at_Tarray_tuchar with (n1 := 4) by (auto; omega); simpl.
  unfold sublist; simpl.
  rewrite split2_data_at_Tarray_tuchar with (n1 := 2) by (auto; omega); simpl.
  unfold sublist; simpl.
  unfold field_address0; simpl.
  rewrite !if_true; try assumption.

  unfold data_at, field_at, at_offset; Intros; simpl.
  rewrite !data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  Intros; unfold unfold_reptype; simpl.
  unfold Znth; simpl.
  rewrite !data_at_rec_eq; simpl.
  rewrite !isptr_offset_val_zero by auto.
  rewrite !sepcon_emp.

  apply sepcon_derives.
  {
    assert (field_compatible tushort [] (offset_val 0 ptr))
      as Hcompat_sin_family.
    {
      pose proof
           (field_compatible_nested_field (Tstruct _sockaddr_in noattr)
                                          [StructField _sin_family] ptr)
        as Hcompat.
      simpl in Hcompat.

      apply Hcompat.
      apply field_compatible_cons.
      simpl.
      split; auto.
      constructor.
      reflexivity.
    }

    assert (field_compatible tushort [] (offset_val 2 ptr))
      as Hcompat_sin_port.
    {
      pose proof
           (field_compatible_nested_field (Tstruct _sockaddr_in noattr)
                                          [StructField _sin_port] ptr)
        as Hcompat.
      simpl in Hcompat.

      apply Hcompat.
      apply field_compatible_cons.
      simpl.
      split; auto.
      right.
      constructor.
      reflexivity.
    }
    
    apply sepcon_derives; 
      apply mapsto_zero_tuchar_join_tushort; auto;
        rewrite isptr_offset_val_zero in *; auto.
  }

  assert (field_compatible (Tstruct _in_addr noattr) [] (offset_val 4 ptr)).
  { 
    
    pose proof
         (field_compatible_nested_field (Tstruct _sockaddr_in noattr)
                                        [StructField _sin_addr] ptr)
      as Hcompat.
    simpl in Hcompat.
    apply Hcompat.
    apply field_compatible_cons.
    simpl.
    split; auto.
    right.
    right.
    repeat constructor.
  }
  
  assert (field_compatible tuint [] (offset_val 4 ptr))
    as Hcompat_sin_addr.
  {
    
    pose proof
         (field_compatible_nested_field (Tstruct _in_addr noattr)
                                        [StructField _s_addr] (offset_val 4 ptr))
      as Hcompat.

    simpl in Hcompat.
    rewrite isptr_offset_val_zero in Hcompat; auto.
    apply Hcompat.
    
    apply field_compatible_cons.
    simpl.
    split; auto.
    repeat constructor.
  }

  repeat rewrite <- sepcon_assoc.
  apply mapsto_zero_tuchar_join_tuint; auto.
  
Qed.

Lemma body_zeroize_addr:
  semax_body Vprog Gprog f_zeroize_addr zeroize_addr_spec.
Proof.
  start_function.

  assert_PROP (field_compatible (Tstruct _sockaddr_in noattr) [] ptr) by entailer!.

  forward_call (ptr, 0, sizeof(Tstruct _sockaddr_in noattr), Tsh).
  {
      
    assert (0 <= 16 < Ptrofs.modulus) as offset_bounded.
    { unfold Ptrofs.modulus.
      unfold Ptrofs.wordsize.
      unfold Wordsize_Ptrofs.wordsize.
      simpl.
      unfold two_power_nat.
      unfold shift_nat.
      simpl.
      omega.
    }
    
    rewrite <- memory_block_data_at_ by assumption.
    pose proof (memory_block_field_compatible_tarraytuchar_ent
                  Tsh 16 ptr offset_bounded).
    simpl.
    apply adjust_sep_apply in H0.
    eapply derives_trans; [apply H0 | ].
    Intros.

    rewrite <- memory_block_data_at__tarray_tuchar_eq; [| assumption].
    entailer!.
  } 
  { split; auto.
    simpl.
    rep_omega.
  } 

  forward.
  
  unfold SocketSpecs.SockAddr.rep_sockaddr.
  simpl.

  apply sockaddr_struct; assumption.

Qed.