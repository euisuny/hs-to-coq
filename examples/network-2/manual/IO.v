Require Import GHC.Base.

From ITree Require Import
     ITree
     Basics.Basics
     Events.State.

From Coq Require Import Lists.List.

Import ITree.Basics.Basics.Monads.
Require Import Network.Socket.Types.

From ExtLib.Structures Require Functor Applicative Monad.

(** *Modeling network relevant I/O operations.

  (An experiment.)
  ""Relevant"" events and effects were crafted from the Network.Socket
  library documentation.

   https://hackage.haskell.org/package/network-3.1.1.1/docs/Network-Socket.html

 *)

(* ====================================================== *)
(** *Network Events

   Network.v defines the corresponding embeddings of
   these uninterpreted events into ITrees. *)
Inductive networkE : Type -> Type :=
| SendE : Socket -> Base.String -> networkE Num.Int
| CloseE : Socket -> networkE unit
| AcceptE : Socket -> networkE (Socket * SockAddr)
| ListenE : Socket -> Num.Int -> networkE unit
| BindE : Socket -> SockAddr -> networkE unit
| SocketE : Family -> SocketType -> Num.Int -> networkE Socket
| SetSocketOptionE : Socket -> SocketOption -> Num.Int -> networkE unit.

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

Definition ioE := networkE.

Definition IO := itree ioE.

(* ====================================================== *)
(** *Mock World state

   We take the conventional(?) perspective of viewing the IO monad
   as handling effects in the effectful (awkward) _World_.

   The model for the mock "network" world is:

   * server: connected port, accepting connections.
     (Only allow one port connection for now. We need decidable equality
      for maintaining a list of ports...)
      - list Socket: current connections
      - Num.Int: maximum number of queued connections.
      - bool: whether server is currently listening on its connection.
   * client: a log of messages it received from the server.
   * sockets: list of available sockets
   *)
Definition server : Type := ((list Socket) * nat * bool).
Definition client : Type := Base.String.
Definition sockets : Type := list Socket.
Definition messages : Type := (list (Socket * Base.String)). (* Could use ext-lib *)
Definition world : Type := server * client * sockets * messages.

(* A couple axioms along the way... *)

(* Assume decidable boolean equality check exists between Sockets. *)
Axiom socket_eq : forall (x y : Socket), {x=y}+{x<>y}.
Axiom socket_eqb : Socket -> Socket -> bool.
Infix "/=?" := socket_eqb (at level 50).
(* Assume there is a function that generates new SockAddrs and Sockets.
   (For `accept`.) *)
Axiom newSockAddr : unit -> SockAddr.
Axiom newSock : unit -> Socket.

Definition valid_socket (sl : list Socket) (x : Socket) : bool :=
  match (List.find (socket_eqb x) sl) with
  | Some _ => true
  | _ => false
  end
.

(* To model the world state, we wish to interpret these events into a
   stateT monad with world information. *)
(* TODO: Factor out "SocketE"'s that are parametrized by a Socket. *)
Definition h_network {E} : networkE ~> stateT world (itree E) :=
  fun _ e '(srv, clnt, skt, msgs) =>
    match e with
    | SendE s x =>
      if valid_socket skt s then
        Ret ((srv, clnt, skt, (s, x)::msgs), 1% Z)
      else
        Ret ((srv, clnt, skt, msgs), 0%Z)
    | CloseE s =>
      if valid_socket skt s then
        Ret ((srv, clnt, remove socket_eq s skt, msgs), tt)
      else
        Ret ((srv, clnt, skt, msgs), tt)
    | AcceptE s =>
      if valid_socket skt s then
        match srv with
        | (ls, n, true) =>
          if length ls <? n then
            Ret (((s::ls, n, true), clnt, skt, msgs), (s, newSockAddr tt))
          else
            Ret (((s::(removelast ls), n, true), clnt, skt, msgs),
                 (s, newSockAddr tt))
        | (_, _, _) => (Ret ((srv, clnt, skt, msgs), (s, newSockAddr tt)))
        end
      else
        Ret ((srv, clnt, skt, msgs), (s, newSockAddr tt))
    | ListenE s n => (* ListenE mutates "global" connection max count... *)
      if valid_socket skt s then
        match srv with
        | (ls, _, false) => Ret (((ls, Z.to_nat n, true), clnt, skt, msgs), tt)
        | (_, _, _) => Ret ((srv, clnt, skt, msgs), tt)
        end
      else
        Ret ((srv, clnt, skt, msgs), tt)
    | BindE s a =>
      if valid_socket skt s then
        match srv with
        | (ls, _, true) => Ret ((srv, clnt, skt, msgs), tt)
        | (_, _, _) => Ret ((srv, clnt, skt, msgs), tt)
        end
      else
        Ret ((srv, clnt, skt, msgs), tt)
    (* Takes in dummy socket generator... *)
    | SocketE _ _ _ => Ret ((srv, clnt, (newSock tt)::skt, msgs), newSock tt)
    (* Ignore this Socket representation, for now. *)
    | SetSocketOptionE f s n => Ret ((srv, clnt, skt, msgs), tt)
    end
.

(* Since there is only one event type (network), handling IO is equivalent to
   handling networks. *)
Definition h_io {E} : ioE ~> stateT world (itree E) := h_network.

Definition interp_io {E A} (t : itree ioE A) : stateT world (itree E) A :=
  interp h_io t.

(* ====================================================== *)
(* Functor/Applicative/Monad laws, taken from wc example. *)

Section Functors.

  Variable f : Type -> Type.

  Context `{Functor.Functor f}.

  Global Instance Functor_Functor : Functor f :=
    fun _ X =>
      X {| fmap__ := fun a b : Type => Functor.fmap;
           op_zlzd____ := fun a b : Type => Functor.fmap ∘ const
        |}.

  Section Applicatives.

    Context `{Applicative.Applicative f}.

    Global Instance Applicative_Applicative : Applicative f :=
      fun _ X =>
        X {| liftA2__ := fun a b c f x y => Applicative.ap (fmap f x) y;
             op_zlztzg____ := fun a b => Applicative.ap ;
             op_ztzg____ := fun a b x y => Applicative.ap (id <$ x) y;
             pure__ := fun a => Applicative.pure
          |}.

    Section Monads.

      Context `{Monad.Monad f}.
      
      Global Instance Monad_Monad : Monad f :=
        fun _ X =>
          X {| op_zgzg____ := fun a b x y => Monad.bind x (fun _ => y);
               op_zgzgze____ := fun a b => Monad.bind ;
               return___ := fun a => Monad.ret
            |}.
      
    End Monads.
  End Applicatives.
End Functors.


Instance Functor_IO : Functor IO := Functor_Functor IO.

Instance Applicative_IO : Applicative IO := Applicative_Applicative IO.

Instance Monad_IO : Monad IO := Monad_Monad IO.
