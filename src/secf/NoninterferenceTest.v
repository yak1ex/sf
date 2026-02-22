Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From SECF Require Import Noninterference.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From SECF Require Import Noninterference.
Import Check.

Goal True.

idtac "-------------------  prove_or_disprove_obvious_f1  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f1".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f1 (
(or (@noninterferent nat nat nat nat obvious_f1)
   (not (@noninterferent nat nat nat nat obvious_f1)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f1.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_obvious_f2  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f2".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f2 (
(or (@noninterferent nat nat nat nat obvious_f2)
   (not (@noninterferent nat nat nat nat obvious_f2)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f2.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f4  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f4".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f4 (
(or (@noninterferent nat nat nat nat less_obvious_f4)
   (not (@noninterferent nat nat nat nat less_obvious_f4)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f4.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f5  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f5".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f5 (
(or (@noninterferent nat nat nat nat less_obvious_f5)
   (not (@noninterferent nat nat nat nat less_obvious_f5)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f5.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f6  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f6".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f6 (
(or (@noninterferent nat nat nat nat less_obvious_f6)
   (not (@noninterferent nat nat nat nat less_obvious_f6)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f6.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f2  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f2".
idtac "Possible points: 1".
check_type @sme_another_insecure_f2 (
(forall pi si : nat,
 @eq (prod nat nat) (@sme nat nat nat nat 0 another_insecure_f2 pi si)
   (@pair nat nat pi (PeanoNat.Nat.add pi si)))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f2.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f3  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f3".
idtac "Possible points: 2".
check_type @sme_another_insecure_f3 (
(forall pi si : nat,
 @eq (prod nat nat) (@sme nat nat nat nat 0 another_insecure_f3 pi si)
   (@pair nat nat pi (PeanoNat.Nat.add pi si)))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f3.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_secure_ex1  --------------------".
idtac " ".

idtac "#> noninterferent_secure_ex1".
idtac "Possible points: 2".
check_type @noninterferent_secure_ex1 ((noninterferent_no_while xpub secure_ex1)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_secure_ex1.
Goal True.
idtac " ".

idtac "-------------------  interferent_insecure_com_explicit  --------------------".
idtac " ".

idtac "#> interferent_insecure_com_explicit".
idtac "Possible points: 2".
check_type @interferent_insecure_com_explicit (
(not (noninterferent_no_while xpub insecure_com_explicit))).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_insecure_com_explicit.
Goal True.
idtac " ".

idtac "-------------------  interferent_insecure_com_implicit  --------------------".
idtac " ".

idtac "#> interferent_insecure_com_implicit".
idtac "Possible points: 3".
check_type @interferent_insecure_com_implicit (
(not (noninterferent_no_while xpub insecure_com_implicit))).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_insecure_com_implicit.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 18".
idtac "Max points - advanced: 18".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- prove_or_disprove_obvious_f1 ---------".
Print Assumptions prove_or_disprove_obvious_f1.
idtac "---------- prove_or_disprove_obvious_f2 ---------".
Print Assumptions prove_or_disprove_obvious_f2.
idtac "---------- prove_or_disprove_less_obvious_f4 ---------".
Print Assumptions prove_or_disprove_less_obvious_f4.
idtac "---------- prove_or_disprove_less_obvious_f5 ---------".
Print Assumptions prove_or_disprove_less_obvious_f5.
idtac "---------- prove_or_disprove_less_obvious_f6 ---------".
Print Assumptions prove_or_disprove_less_obvious_f6.
idtac "---------- sme_another_insecure_f2 ---------".
Print Assumptions sme_another_insecure_f2.
idtac "---------- sme_another_insecure_f3 ---------".
Print Assumptions sme_another_insecure_f3.
idtac "---------- noninterferent_secure_ex1 ---------".
Print Assumptions noninterferent_secure_ex1.
idtac "---------- interferent_insecure_com_explicit ---------".
Print Assumptions interferent_insecure_com_explicit.
idtac "---------- interferent_insecure_com_implicit ---------".
Print Assumptions interferent_insecure_com_implicit.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-01-07 13:38 *)

(* 2026-01-07 13:38 *)
