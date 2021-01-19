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
