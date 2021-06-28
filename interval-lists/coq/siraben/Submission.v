Require Import Defs.
Require Import Psatz.
Require Import Arith.
Open Scope nat.

(*
Define complement and intersection operations for interval lists, and prove them correct!
*)

(* complement *)

Fixpoint compl' (n : nat) (l : intervals) :=
  match l with
  | [] => [ [n, +oo) ]
  | [ [S a, +oo) ] => [ [n, S a) ]
  | [l, r) :: xs => (* [n, l) :: compl' r xs *)
    match l with
    | 0 => compl' r xs
    | _ => [n, l) :: compl' r xs
    end
  | _ => []
  end.

Definition compl (l : intervals) := compl' 0 l.

Example ex1 : intervals := [ [1,3) ; [5,6) ;  [9, +oo) ].

Eval compute in (compl [[0, +oo )]).
Eval compute in (compl ex1).
Eval compute in (compl (compl ex1)).
Eval compute in (compl [[1,4);[6,9)]).
Eval compute in (compl [[0, +oo)]).

Theorem invariant_complement ins :
  inv ins ->
  inv (compl ins).
Proof.
  induction ins;  intros Hins.
  - cbv. auto with arith.
  - cbn. destruct a, ins, imax, imin; try (cbn; lia).
    + cbn in *.
      repeat split; try lia.
    + Eval compute in (compl [[0, +oo )]).
      cbn.
      destruct i, imax, imin, ins; try (cbn in *; lia).
      cbn.
      cbn in Hins.
      destruct i, imax, imin0; repeat split; try lia.
      * cbn in *.
        destruct Hins as [? [? [? [? [? [? ?]]]]]].
        apply IHins. repeat split; try lia.
        assumption.
      * destruct ins.
        2: lia.
        apply IHins. cbn. lia.
    + destruct i, imax, imin0; repeat split; try (cbn in *; lia).
      * cbn in *. apply IHins.
        repeat split; try lia.
        destruct Hins as [? [? [? [? ?]]]].
        assumption.
      * cbn in *.
        destruct ins; try lia.
        cbn. lia.
Qed.

Theorem set_of_is_complement ins :
  inv ins ->
  set_of (compl ins) ≡ ∁ (set_of ins).
Proof.
Admitted.
