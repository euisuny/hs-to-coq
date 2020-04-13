Require Import GHC.Base.
From ExtLib.Structures Require Functor Applicative Monad.
From ITree Require Import
     ITree
     Basics.Basics
     Events.State.

From Coq Require Import Lists.List
     String.

Require Import NetworkTypes ServerDefs SpecEffect.
(* Require Import DeepWeb.Lib.Socket DeepWeb.Lib.SocketInterface DeepWeb.Lib.Util Map DeepWeb.Lib.NetworkInterface. *)

(* Import SocketAPI.  *)
Import ListNotations.

(** *Modeling network relevant I/O operations.

  (An experiment.)
  ""Relevant"" events and effects were crafted from the Network.Socket
  library documentation.

   https://hackage.haskell.org/package/network-3.1.1.1/docs/Network-Socket.html

 *)

Definition Socket := SocketModel.sockfd.

(* ====================================================== *)
(** *Haskell Network Events

   Network.v defines the corresponding embeddings of
   these uninterpreted events into ITrees.

   These are "axiomiatized" translations of relevant network effects, which
   can be automatically generated.
 *)
Inductive haskE : Type -> Type :=
| SendE : Socket -> bytes -> haskE Num.Int
| CloseE : Socket -> haskE unit
| AcceptE : Socket -> haskE (Socket * SockAddr)
| ListenE : Socket -> Num.Int -> haskE unit
| BindE : Socket -> SockAddr -> haskE unit
| SocketE : Family -> SocketType -> Num.Int -> haskE Socket
| SetSocketOptionE : Socket -> SocketOption -> Num.Int -> haskE unit.

(* ====================================================== *)
(** *Composing IO Events

   Alternatively, if we wanted to model _different IO events_, we can
   use the sum operator to combine different events.

   For instance, we can define the following:

   (* Read/write event to STDIN. *)
   Inductive rwE : Type -> Type :=
   | ReadEff : rwE unit
   | WriteEff : rwE unit
   .

   Definition ioE := rwE +' networkE.

   Using subevents, we can also compose different events. For now, we
   only focus on single-threaded network events.
 *)
Require Import ITree.Events.Nondeterminism ITree.Events.Exception.

(*   Definition or {E X} `{nondetE -< E} (k1 k2 : itree E X) : itree E X := *)
(*     Vis (convert Or) (fun x : bool => if x then k1 else k2). *)

Definition ioE := haskE +' (exceptE string) +' nondetE.

(* The above way of dealing with subevents (using `convert`) is a deprecated version
   (also probably unsound) from the DeepWeb experiment.
   Need to work around with the current model of subevents with ITrees. For now,
   use haskE instead of ioE.
 *)
Definition IO := itree haskE.

From ExtLib Require Import Functor Applicative Monad. 
(* ====================================================== *)
(* Functor/Applicative/Monad laws, taken from wc example. *)

Section Functors.

  Variable f : Type -> Type.

  Context `{Functor.Functor f}.

  Global Instance Functor_Functor : Base.Functor f :=
    fun _ X =>
      X {| fmap__ := fun a b : Type => Functor.fmap;
           op_zlzd____ := fun a b : Type => Functor.fmap ∘ const
        |}.

  Section Applicatives.

    Context `{Applicative.Applicative f}.

    Global Instance Applicative_Applicative : Base.Applicative f :=
      fun _ X =>
        X {| liftA2__ := fun a b c f x y => Applicative.ap (fmap f x) y;
             op_zlztzg____ := fun a b => Applicative.ap ;
             op_ztzg____ := fun a b x y => Applicative.ap (id <$ x) y;
             pure__ := fun a => Applicative.pure
          |}.

    Section Monads.

      Context `{Monad.Monad f}.
      
      Global Instance Monad_Monad : Base.Monad f :=
        fun _ X =>
          X {| op_zgzg____ := fun a b x y => Monad.bind x (fun _ => y);
               op_zgzgze____ := fun a b => Monad.bind ;
               return___ := fun a => Monad.ret
            |}.
      
    End Monads.
  End Applicatives.
End Functors.

Instance Functor_IO : Base.Functor IO := Functor_Functor IO.

Instance Applicative_IO : Base.Applicative IO := Applicative_Applicative IO.

Instance Monad_IO : Base.Monad IO := Monad_Monad IO.
