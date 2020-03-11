(* Total maps *)

(* This module is meant to be [Require]-d but not [Import]-ed. *)

From Coq Require Import Setoid Morphisms Logic.FunctionalExtensionality.

From QuickChick Require Import Decidability.

Set Bullet Behavior "Strict Subproofs".

Section Map.

Variable K V : Type.
Context `{Dec_Eq K}.

Definition t : Type := K -> V.

Definition update : K -> V -> t -> t :=
  fun k0 v0 f k => if k = k0 ? then v0 else f k.

Definition lookup : t -> K -> V := fun f => f.

Definition modify : K -> (V -> V) -> t -> t :=
  fun k m f => update k (m (lookup f k)) f.

Lemma update_lookup_eq k k' v m :
  k = k' ->
  lookup (update k v m) k' = v.
Proof.
  intro Hk.
  unfold lookup.
  unfold update.
  destruct dec.
  - auto.
  - subst; contradiction.
Qed.

Lemma update_lookup_neq k k' v m :
  k <> k' ->
  lookup (update k v m) k' = lookup m k'.
Proof.
  intros Hk.
  unfold lookup.
  unfold update.
  destruct dec.
  - subst; contradiction.
  - auto.
Qed.

Lemma update_update_eq k k' v v' m :
  k = k' ->
  update k v (update k' v' m) = update k v m.
Proof.
  intro Hk; subst k'.
  apply functional_extensionality.
  intro k2.
  unfold update.
  destruct dec; auto.
Qed.

Lemma lookup_update_eq k k' v m :
  k = k' ->
  v = lookup m k' ->
  update k v m = m.
Proof.
  intros; apply functional_extensionality; intro.
  unfold update.
  destruct dec; subst; auto.
Qed.

Lemma modify_modify_eq k f g m :
  modify k f (modify k g m) = modify k (fun st => f (g st)) m.
Proof.
  apply functional_extensionality; intro.
  unfold modify, update, lookup.
  destruct dec; auto.
  destruct dec; auto.
  contradiction.
Qed.

End Map.

Arguments t K V : assert.
Arguments update {K V _}.
Arguments lookup {K V}.
Arguments modify {K V _}.
