Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set :=
| Plus
| Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Check mult.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

(* syntactic sugar *)

Definition binopDenoteReal : binop -> nat -> nat -> nat :=
  fun (b : binop) => match b with
                  | Plus => plus
                  | Times => mult
                  end.

(* CIC enjoys properties like strong normalization and relative consistency *)

(* every Coq source file is a series of vernacular commands, where many command forms take arguments that are Gallina or Ltac programs. *)

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* Unlike with ML, which hardcodes an eager reduction strategy,
   or Haskell, which hardcodes a lazy strategy,
   in Coq we are free to choose between these and many other orders of evaluation,
   because all Coq programs terminate. *)

Eval simpl in expDenote (Const 42).
Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b => match s with
               | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
               | _ => None
               end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' =>
    match instrDenote i s with
    | None => None
    | Some s' => progDenote p' s'
    end
  end.

Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Lemma compile_correct' : forall e p s,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e.
  - intros. unfold expDenote.
    unfold progDenote at 1. simpl. fold progDenote.
    reflexivity.
  (* Hypos are based on term e1 e2 *)
  - intros.
    unfold compile. fold compile.
    unfold expDenote. fold expDenote.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    simpl. reflexivity.
Qed.

Lemma compile_correct'' : forall e s p,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

Theorem compile_correct : forall e,
    progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intro e.
  rewrite (app_nil_end (compile e)).
  apply compile_correct'.
Qed.

(* Coq uses case-sensitive variable names *)

Inductive type : Set :=
| Nat
| Bool.

(* We define tbinop as an indexed type family.
   Indexed inductive types are at the heart of Coq’s expressive power;
   almost everything else of interest is defined in terms of them *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

(* ML and Haskell have indexed algebraic datatypes.
   For instance, their list types are indexed by the type of data that the list carries.
   However, compared to Coq, ML and Haskell 98 place two important restrictions on datatype definitions. *)

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.


Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res) : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => beq_nat
  | TEq Bool => eqb
  | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

(* I bet first examples are very confused to me ! *)
