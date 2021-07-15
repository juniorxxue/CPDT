Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Print False.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    elimtype False.
    crush.
  Qed.

  Print and.

  Print prod.

  Theorem and_comm : P /\ Q -> Q /\ P.
    destruct 1.
    split; eauto.
  Qed.

  Print or.

  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right. assumption.
    left. assumption.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.
  
End Propositional.

(* we can only prove these tautologies when P is decidable *)

(* A formula P -> Q is equivalent to forall x : P, Q where x does not appear in Q *)

Print ex.

Theorem exist1 : exists x : nat, x + 1 = 2.
  exists 1.
  reflexivity.
Qed.

Theorem exist2 :
  forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  destruct 1.
  rewrite <- H.
  crush.
Qed.

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Print eq.

(* equliaty is defined as the least reflexive relation *)

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  inversion 1.
Qed.

Check isZero_ind.

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.
  destruct n; destruct n0; crush.
  SearchRewrite (_ + S _).
  rewrite <- plus_n_Sm in H0.
  apply IHeven with n0; assumption.
  Restart.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
    | [H: S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
    end; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

Lemma even_contra'' : forall n' n, even n' -> n' = S (n + n) -> False.
  induction 1; crush;
  match goal with
  | [H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
  end; crush.
Abort.


