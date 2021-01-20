Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.*)

Check (fun x : nat => x).
Check (fun x : True => x).

(* The identity program is interpreted as a proof that True, the always-true proposition, implies itself *)

Check I.

Check (fun _ : False => I).

(* Every one of these example programs whose type looks like a logical formula is a proof term *)

(* One glib answer is that True and False are types, but true and false are not. *)

(* A more useful answer is that Coq’s metatheory guarantees that any term of *)
(* type bool evaluates to either true or false.
   This means that we have an algorithm for an- swering any question phrased as an expression of type bool.
   Conversely, most propositions do not evaluate to True or False;
   the language of inductively defined propositions is much richer than that.  *)
