Require Import List.
Import ListNotations.

From Custom Require Export
     Monad.
Import MonadNotations.
Open Scope monad_scope.

(** * Interaction Trees. *)
(** ** Basic Definitions *)

(* The core definition of ITrees.  An [itree E R] is the denotation of
   a program as coinductive (possibly infinite) tree where the leaves
   are [Ret] nodes labeled with return values from [R] and each
   internal nodes is either an "internal" [Tau] node with one child or
   else a "external" [Vis] node with a visible effect of type [E X]
   plus a continuation [k] that receives a [X] value as a response
   to that effect.
 *)

CoInductive itree (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis (X : Type) (e : E X) (k : X -> itree E R)
| Tau (t : itree E R).

Arguments Ret {E R} r.
Arguments Vis {E R X} e k.
Arguments Tau {E R} t.

(* The type [itree] is commonly known as the "Freer monad" -- see
   _Freer Monads, More Extensible Effects_, by Oleg Kiselyov and
   Hiromi Ishii. *)

(** ** Monad Structure *)

Module Core.

Definition bind_body' {E R S}
           (s : itree E R)
           (go : itree E R -> itree E S)
           (h : R -> itree E S) : itree E S :=
  match s with
  | Ret r => h r
  | Vis e k => Vis e (fun x => go (k x))
  | Tau t => Tau (go t)
  end.

Definition bind_itree {E R S}
           (s : itree E R) (h : R -> itree E S) : itree E S :=
  (cofix go (s : itree E R) :=
      bind_body' s go h) s.

(* [itree E] forms a [Monad] (for any type of events [E]). *)
Definition Monad_itree E : Monad (itree E) := {|
    ret _ := Ret;
    bind _ _ := bind_itree;
  |}.

End Core.

(* However, it is convenient to slightly change the bind operation to
   insert a [Tau] in the case where the right-hand argument to bind is
   just a [Ret], to make programs/specifications neater and easier to
   write.  With this variant of bind, [itree] is no longer a monad
   strictly speaking, but it remains one in a looser sense where we
   ignore [Tau] such that [Tau t] is considered equivalent to [t]. *)
Definition bind_itree {E R S}
           (s : itree E R) (h : R -> itree E S) : itree E S :=
  Core.bind_itree s (fun r => Tau (h r)).

Instance Monad_M E : Monad (itree E) := {|
    ret _ := Ret;
    bind _ _ := bind_itree;
  |}.

(* Lift a single effect to an [itree] action. *)
Definition liftE {E} {X} (e : E X) : itree E X :=
  Vis e (fun x => Ret x).

(** ** Handy Utilities *)

(* A number of useful ITrees and ITree combinators *)

(* An ITree representing an infinite loop *)
CoFixpoint spin {E} {R} : itree E R := Tau spin.

(* An ITree that does one internal step and then returns. *)
Definition tick {E} : itree E unit := Tau (Ret tt).

(* The void type is useful as a return type to [itree], to enforce the
    constraint that a given computation should never terminate. *)
Inductive void : Type := .

(* An infinite loop with a given body. *)
CoFixpoint forever {E} {R} (x : itree E R) : itree E void :=
  x ;; forever x.

(* A one-sided conditional. *)
Definition when {E} (b : bool) (body : itree E unit)
                : itree E unit :=
  if b then body else ret tt.

(* An imperative "for each" loop over a list. *)
CoFixpoint for_each {E A} (bs : list A) (body : A -> itree E unit)
                  : itree E unit :=
  match bs with
  | [] => ret tt
  | b :: bs' => body b;; for_each bs' body
  end.

(* An imperative while-loop combinator. *)
CoFixpoint while {E : Type -> Type} {T : Type}
                 (cond : T -> bool)
                 (body : T -> itree E T)
               : T -> itree E T :=
  fun t =>
    match cond t with
    | true =>
      r <- body t ;;
      while cond body r
    | false => ret t
    end.

(* Stateful infinite loop. *)
CoFixpoint loop_with_state {E S void}
           (body : S -> itree E S)
           (s : S) : itree E void :=
  body s >>= loop_with_state body.

(* Wrap a function around the results returned from an ITree *)
Definition map_itree {E R S}
           (f : R -> S) (s : itree E R) : itree E S :=
  let cofix go (s : itree E R) :=
      match s with
      | Ret r => Ret (f r)
      | Vis e k => Vis e (fun x => go (k x))
      | Tau t => Tau (go t)
      end
  in go s.

(* Ignore the results from an ITree (changing it to have [unit] result type) *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map_itree (fun _ => tt).

(* Transform every [Vis] node in the tree. *)
CoFixpoint hoist {E F X}
           (f : forall Z, E Z -> F Z)
           (m : itree E X)
  : itree F X :=
  match m with
  | Ret x => Ret x
  | Vis e k => Vis (f _ e) (fun z => hoist f (k z))
  | Tau n => Tau (hoist f n)
  end.

Delimit Scope itree_scope with itree.

Infix ">>=" := bind_itree : itree_scope.
Infix ">>=0" := Core.bind_itree (at level 50) : itree_scope.

Local Open Scope itree_scope.

(* In order to unfold a cofixpoint we have to rewrite it with
   [match_itree]. *)
Notation id_itree i :=
  match i with
  | Ret r => Ret r
  | Vis e k => Vis e k
  | Tau t => Tau t
  end.

Lemma match_itree {E X} (i : itree E X) : i = id_itree i.
Proof. destruct i; auto. Qed.

Definition core_bind_body {E X Y} s (k : X -> itree E Y) :=
  Core.bind_body' s (fun s => Core.bind_itree s k) k.

Lemma core_bind_def {E X Y} s (k : X -> itree E Y) :
  Core.bind_itree s k = core_bind_body s k.
Proof.
  intros.
  rewrite (match_itree (Core.bind_itree _ _)).
  destruct s; auto.
  simpl.
  rewrite <- match_itree.
  auto.
Qed.

Definition bind_body {E X Y} s (k : X -> itree E Y) :=
  Core.bind_body' s (fun s' => bind_itree s' k) (fun x => Tau (k x)).

Lemma bind_def {E X Y} s (k : X -> itree E Y) :
  bind_itree s k = bind_body s k.
Proof.
  unfold bind_itree.
  rewrite core_bind_def.
  auto.
Qed.

(* Some basic equations *)

Module Export Basics.

Lemma ret_bind0 {E R S} (r : R) (k : R -> itree E S) :
  Core.bind_itree (Ret r) k = k r.
Proof.
  rewrite core_bind_def.
  reflexivity.
Qed.

Lemma ret_bind {E R S} (r : R) (k : R -> itree E S) :
  bind_itree (Ret r) k = Tau (k r).
Proof.
  unfold bind_itree.
  rewrite ret_bind0.
  reflexivity.
Qed.

Lemma vis_bind {E A B X} (e : E X) (k : X -> itree E A) (h : A -> itree E B) :
  (Vis e k >>= h) =
  (Vis e (fun x => k x >>= h)).
Proof.
  rewrite bind_def. reflexivity.
Qed.

Lemma tau_bind {E A B} (t : itree E A) (k : A -> itree E B) :
  (Tau t >>= k) = Tau (t >>= k).
Proof.
  rewrite bind_def. reflexivity.
Qed.

Lemma while_loop_unfold :
  forall {E T} (cond : T -> bool) (P : T -> itree E T) (t : T),
    while cond P t = if cond t then
                       (P t >>= fun r => while cond P r)
                     else ret t.
Proof.
  intros.
  rewrite (match_itree (while _ _ _)).
  simpl.
  destruct (cond t);
    auto.
  rewrite <- match_itree.
  reflexivity.
Qed.

Lemma loop_with_state_unfold :
  forall {E S void} (body : S -> itree E S) (s : S),
    @loop_with_state E S void body s = body s >>= loop_with_state body.
Proof.
  intros.
  rewrite (match_itree (loop_with_state _ _)); simpl.
  rewrite (match_itree (_ >>= _)); simpl.
  do 2 rewrite <- match_itree.
  reflexivity.
Qed.

End Basics.

Module Monad.

Import MonadNotations.
Local Open Scope monad_scope.

Lemma ret_bind {E R S} (r : R) (k : R -> itree E S) :
  Ret r >>= k = Tau (k r).
Proof.
  simpl; apply Basics.ret_bind.
Qed.

Lemma vis_bind {E A B X} (e : E X) (k : X -> itree E A) (h : A -> itree E B) :
  (Vis e k >>= h) =
  (Vis e (fun x => k x >>= h)).
Proof. simpl; apply Basics.vis_bind. Qed.

Lemma tau_bind {E A B} (t : itree E A) (k : A -> itree E B) :
  (Tau t >>= k) = Tau (t >>= k).
Proof. simpl; apply Basics.tau_bind. Qed.

Lemma while_loop_unfold :
  forall {E T} (cond : T -> bool) (P : T -> itree E T) (t : T),
    while cond P t = if cond t then
                       (P t >>= fun r => while cond P r)
                     else ret t.
Proof.
  simpl; apply @Basics.while_loop_unfold.
Qed.

End Monad.
