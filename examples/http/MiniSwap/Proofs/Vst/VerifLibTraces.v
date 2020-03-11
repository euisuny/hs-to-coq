From DeepWeb.Free.Monad Require Import Traces.

From DeepWeb.Spec
     Require Import Swap_ImplModel
     Vst.SocketSpecs Vst.MainInit Vst.MonadExports.

From DeepWeb.Lib
     Require Import VstLib.

Import TracePred.
Import SockAPIPred.

Lemma trace_incl_respects_bind_assoc {X Y Z}
      (m : itree socketE X)
      (f : X -> itree socketE Y)
      (g : Y -> itree socketE Z)
      (t : itree socketE Z) :
  ((' b <- (' a <- m ;; f a);; g b) <= t)%trace ->
  ((' a <- m;; 'b <- f a;; g b) <= t)%trace.
Proof. apply Traces.trace_incl_respects_bind_assoc. Qed.

Lemma trace_or_incl_bind1 {X Y}
      (m1 m2 : itree socketE X) (k : X -> itree socketE Y) :
  ((x <- m1;; k x) <= (x <- disj (m1 | m2)%nondet;; k x))%trace.
Proof. pose proof (Traces.trace_or_incl_bind1 m1 m2 k) as H. apply H.
Qed.

Lemma trace_incl_refl {R} (m : itree socketE R) : (m <= m)%trace.
Proof. apply Traces.trace_incl_refl. Qed.

Lemma trace_or_incl {R} (k1 k2 : itree socketE R) :
  (k1 <= disj (k1 | k2)%nondet)%trace /\
  (k2 <= disj (k1 | k2)%nondet)%trace.
Proof. pose proof (Traces.trace_or_incl k1 k2) as H. apply H. Qed.
