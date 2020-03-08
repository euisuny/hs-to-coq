Require Export String.

Require Import Omega.

Definition zero := String Ascii.zero EmptyString.

Lemma app_string_length (s1 s2 : string):
  String.length (s1 ++ s2) = (String.length s1 + String.length s2)%nat.
Proof.
  revert s2.
  induction s1; auto.
  intros s2.
  simpl.
  f_equal.
  apply IHs1.
Qed.

Lemma string_app_assoc (s1 s2 s3 : string):
  (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
Proof.
  revert s2.
  induction s1; auto; intros s2.
  simpl.
  f_equal.
  rewrite IHs1.
  reflexivity.
Qed.

Lemma string_app_nil_r (s : string):
  (s ++ "")%string = s.
Proof.
  induction s; simpl; auto; rewrite IHs; auto.
Qed.

Fixpoint string_firstn (n : nat) (str : string) :=
  match n with
  | 0%nat => ""%string
  | S n' =>
    match str with
    | ""%string => ""%string
    | String s str' =>
      String s (string_firstn n' str')
    end
  end.

Fixpoint string_skipn (n : nat) (str : string) :=
  match n with
  | 0%nat => str
  | S n' =>
    match str with
    | ""%string => ""%string
    | String s str' =>
      string_skipn n' str'
    end
  end.

Lemma string_firstn_empty (n : nat): string_firstn n "" = ""%string.
Proof.
  destruct n; auto.
Qed.

Lemma string_firstn_skipn (n : nat) (str : string):
  str = (string_firstn n str ++ string_skipn n str)%string.
Proof.
  revert str; induction n; intros str; simpl; auto.
  destruct str; auto.
  unfold String.append.
  fold String.append.
  f_equal.
  apply IHn.
Qed.

Lemma string_length_firstn (n : nat) (str : string):
  String.length (string_firstn n str) = Nat.min n (String.length str).
Proof.
  revert str.
  induction n; intros str.
  - auto.
  - destruct str as [| a str]; auto.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma string_length_skipn (n : nat) (str: string):
  String.length (string_skipn n str) = (String.length str - n)%nat.
Proof.
  revert str.
  induction n; intros str.
  - simpl.
    omega.
  - destruct str as [| a str]; auto.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma string_skipn_empty (n : nat) :
  string_skipn n ""%string = ""%string.
Proof.
  destruct n; simpl; auto.
Qed.

Lemma string_firstn_same (n : nat) (s : string):
  (n >= String.length s)%nat -> string_firstn n s = s.
Proof.
  revert s.
  induction n; intros s Hn.
  - destruct s; simpl in Hn; try omega. reflexivity.
  - destruct s; auto.
    simpl.
    f_equal; rewrite IHn; auto.
    simpl in Hn. omega.
Qed.

Lemma string_skipn_length (n : nat) (str : string):
  (String.length str <= n)%nat -> string_skipn n str = ""%string.
Proof.
  revert n.
  induction str; intros.
  - apply string_skipn_empty.
  - destruct n.
    + simpl in H; omega.
    + simpl in *.
      rewrite IHstr; auto.
      apply le_S_n in H.
      trivial.
Qed.

Lemma string_firstn_app1 (n : nat) (s1 s2 : string):
  (n <= String.length s1)%nat
  -> string_firstn n (s1 ++ s2) = string_firstn n s1.
Proof.
  revert s1 s2.
  induction n; intros s1 s2 Hn.
  - reflexivity.
  - destruct s1.
    + simpl in Hn; omega.
    + simpl in Hn.
      apply le_S_n in Hn.
      simpl.
      f_equal.
      rewrite IHn; try omega.
      reflexivity.
Qed.

Lemma string_firstn_app2 (n : nat) (s1 s2 : string):
  (n >= String.length s1)%nat
  -> string_firstn n (s1 ++ s2) = (s1 ++ string_firstn (n - String.length s1) s2)%string.
Proof.
  revert s1 s2.
  induction n; intros s1 s2 Hn.
  - simpl.
    destruct s1; auto. simpl in Hn; omega.
  - destruct s1.
    + simpl in Hn.
      simpl append.
      reflexivity.
    + simpl.
      f_equal.
      apply IHn.
      simpl in Hn.
      apply le_S_n in Hn.
      omega.
Qed.

Lemma string_skipn_app1 (n : nat) (s1 s2 : string):
  (n <= String.length s1)%nat
  -> string_skipn n (s1 ++ s2) = (string_skipn n s1 ++ s2)%string.
Proof.
  revert s1 s2.
  induction n; intros s1 s2 Hn; try reflexivity.
  destruct s1.
  - simpl in Hn; omega.
  - simpl in Hn.
    simpl.
    rewrite IHn; trivial.
    apply le_S_n in Hn; trivial.
Qed.

Lemma string_skipn_app2 (n : nat) (s1 s2 : string):
  (n >= String.length s1)%nat
  -> string_skipn n (s1 ++ s2) = string_skipn (n - String.length s1) s2.
Proof.
  revert s1 s2.
  induction n; intros s1 s2 Hn.
  - destruct s1; simpl in *; try omega; trivial.
  - destruct s1; auto.
    simpl.
    rewrite IHn; trivial.
    apply le_S_n in Hn; trivial.
Qed.

Lemma string_skipn_skipn (n m : nat) (s : string):
  string_skipn n (string_skipn m s) = string_skipn (m + n)%nat s.
Proof.
  revert n s.
  induction m; intros n s; try reflexivity.
  destruct s.
  - simpl. rewrite string_skipn_empty. reflexivity.
  - simpl.
    rewrite IHm; trivial.
Qed.

Lemma string_firstn_no_overflow (n : nat) (s1 s2 : string):
  string_firstn n s1 = s2
  -> n = String.length s2 -> n <= String.length s1.
Proof.
  intros Hfirst ?; subst n.
  destruct (length s1 <=? length s2) eqn:Hle.
  - apply Nat.leb_le in Hle; trivial.
    rewrite string_firstn_same in Hfirst by assumption.
    subst; trivial.
  - apply Nat.leb_gt in Hle.
    omega.
Qed.

Lemma substring_firstn (n : nat) (str : string):
  substring 0 n str = string_firstn n str.
Proof.
  revert str.
  induction n.
  - simpl.
    destruct str; auto.
  -  simpl.
     destruct str; auto.
     simpl.
     f_equal.
     apply IHn.
Qed.

Lemma substring_firstn_skipn (n m : nat) (str: string):
  substring n m str = string_firstn m (string_skipn n str).
Proof.
  revert m str.
  induction n; intros m str.
  - simpl.
    apply substring_firstn.
  - destruct str as [| a str].
    + simpl.
      destruct m; auto.
    + simpl.
      rewrite IHn; auto.
Qed.

Lemma substring_skipn_firstn (n m : nat) (str: string):
  substring n m str = string_skipn n (string_firstn (n + m) str).
Proof.
  revert m str.
  induction n; intros m str.
  - simpl.
    apply substring_firstn.
  - destruct str as [| a str].
    + simpl.
      destruct m; auto.
    + simpl.
      rewrite IHn; auto.
Qed.

Lemma substring_in_bounds (i : nat) (s1 s2 : string):
  (s1 <> ""%string)
  -> substring i (String.length s1) s2 = s1
  -> i + String.length s1 <= String.length s2.
Proof.
  rewrite substring_firstn_skipn.
  revert s1 s2.
  induction i; intros s1 s2 NotEmpty Hfirstn.
  - simpl in Hfirstn.
    rewrite <- Hfirstn.
    rewrite string_length_firstn.
    simpl.
    apply Nat.min_le_iff.
    right; trivial.
  - destruct s2.
    + destruct s1 eqn:Hs1; try discriminate.
      simpl in Hfirstn.
      contradiction.
    + simpl in Hfirstn.
      specialize (IHi s1 s2 NotEmpty Hfirstn).
      simpl.
      apply le_n_S.
      trivial.
Qed.

Fixpoint string_fold_left {A} (f : A -> Ascii.ascii -> A)
         (s : string)
         (accum: A) :=
  match s with
  | EmptyString => accum
  | String a s' => string_fold_left f s' (f accum a)
  end.

Module Export String_List.

Import List.
Import ListNotations.

Fixpoint string_map {A} (f : Ascii.ascii -> A) (s : string) : list A :=
  match s with
  | EmptyString => []
  | String a s' => (f a) :: string_map f s'
  end.

Lemma string_map_app {A} (f : Ascii.ascii -> A) (s1 s2 : string):
  string_map f (s1 ++ s2) = string_map f s1 ++ string_map f s2.
Proof.
  revert s2.
  induction s1; intros s2; simpl; auto; f_equal; auto.
Qed.

Lemma string_map_firstn {A} (f : Ascii.ascii -> A) (n : nat) (s : string):
  string_map f (string_firstn n s) = List.firstn n (string_map f s).
Proof.
  revert s.
  induction n; intros s; auto.
  destruct s; auto.
  simpl.
  f_equal; rewrite IHn; reflexivity.
Qed.

Lemma string_map_skipn {A} (f : Ascii.ascii -> A) (n : nat) (s : string):
  string_map f (string_skipn n s) = List.skipn n (string_map f s).
Proof.
  revert s.
  induction n; intros s; auto.
  destruct s; auto.
  simpl.
  f_equal; rewrite IHn; reflexivity.
Qed.

Lemma list_map_string_map {A B} (f : Ascii.ascii -> A) (g : A -> B)
      (n : nat) (s : string):
  List.map g (string_map f s) = string_map (fun a => g (f a)) s.
Proof.
  induction s; auto.
  simpl; f_equal; auto.
Qed.

Fixpoint string_of_ascii_list (l : list Ascii.ascii) : string :=
  match l with
  | [] => EmptyString
  | (a :: xs) =>
    String a (string_of_ascii_list xs)
  end.

Definition ascii_list_of_string (s : string) : list Ascii.ascii :=
  string_map id s.

Lemma ascii_list_to_string_id l : ascii_list_of_string (string_of_ascii_list l) = l.
Proof.
  unfold ascii_list_of_string.
  induction l; simpl; f_equal; auto.
Qed.

Lemma string_to_ascii_list_id l : string_of_ascii_list (ascii_list_of_string l) = l.
Proof.
  induction l; auto.
  simpl; f_equal; auto.
Qed.

Lemma ascii_list_of_string_app (s1 s2 : string):
  ascii_list_of_string (s1 ++ s2)
  = ascii_list_of_string s1 ++ ascii_list_of_string s2.
Proof.
  unfold ascii_list_of_string.
  apply string_map_app.
Qed.

Lemma string_of_ascii_list_app (a1 a2 : list Ascii.ascii):
  string_of_ascii_list (a1 ++ a2) =
  (string_of_ascii_list a1 ++ string_of_ascii_list a2)%string.
Proof.
  rewrite <- string_to_ascii_list_id.
  rewrite ascii_list_of_string_app.
  rewrite !ascii_list_to_string_id.
  reflexivity.
Qed.

Lemma ascii_list_of_string_firstn (n : nat) (s : string):
  ascii_list_of_string (string_firstn n s) =
  List.firstn n (ascii_list_of_string s).
Proof.
  unfold ascii_list_of_string.
  rewrite string_map_firstn.
  reflexivity.
Qed.

Lemma ascii_list_of_string_skipn (n : nat) (s : string):
  ascii_list_of_string (string_skipn n s) =
  List.skipn n (ascii_list_of_string s).
Proof.
  unfold ascii_list_of_string.
  rewrite string_map_skipn.
  reflexivity.
Qed.

Lemma string_fold_left_list_fold_left {A} (f: A -> Ascii.ascii -> A)
      (s : string) (accum : A):
  string_fold_left f s accum = List.fold_left f (string_map id s) accum.
Proof.
  revert accum.
  induction s; simpl; auto.
Qed.

Lemma string_fold_left_app {A : Type} (f : A -> Ascii.ascii -> A) (accum : A)
      (s1 s2 : string):
  string_fold_left f (s1 ++ s2) accum
  = string_fold_left f s2 (string_fold_left f s1 accum).
Proof.
  rewrite string_fold_left_list_fold_left.
  rewrite string_map_app.
  rewrite fold_left_app.
  rewrite <- !string_fold_left_list_fold_left.
  reflexivity.
Qed.

End String_List.