Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From SECF Require Import StaticIFC.

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

From SECF Require Import StaticIFC.
Import Check.

Goal True.

idtac "-------------------  not_cf_wt_noninterferent_com  --------------------".
idtac " ".

idtac "#> not_cf_wt_noninterferent_com".
idtac "Possible points: 1".
check_type @not_cf_wt_noninterferent_com (
(not
   (cf_well_typed xpub (CIf (BEq (AId Y) (ANum 0)) (CAsgn Z (ANum 0)) CSkip)))).
idtac "Assumptions:".
Abort.
Print Assumptions not_cf_wt_noninterferent_com.
Goal True.
idtac " ".

idtac "-------------------  ts_typechecker  --------------------".
idtac " ".

idtac "#> ts_typechecker".
idtac "Possible points: 2".
check_type @ts_typechecker ((forall (_ : pub_vars) (_ : label) (_ : com), bool)).
idtac "Assumptions:".
Abort.
Print Assumptions ts_typechecker.
Goal True.
idtac " ".

idtac "-------------------  ts_typechecker_sound  --------------------".
idtac " ".

idtac "#> ts_typechecker_sound".
idtac "Possible points: 2".
check_type @ts_typechecker_sound (
(forall (P : pub_vars) (pc : label) (c : com)
   (_ : @eq bool (ts_typechecker P pc c) true),
 ts_well_typed P pc c)).
idtac "Assumptions:".
Abort.
Print Assumptions ts_typechecker_sound.
Goal True.
idtac " ".

idtac "-------------------  ts_typechecker_complete  --------------------".
idtac " ".

idtac "#> ts_typechecker_complete".
idtac "Possible points: 2".
check_type @ts_typechecker_complete (
(forall (P : pub_vars) (pc : label) (c : com)
   (_ : @eq bool (ts_typechecker P pc c) false),
 not (ts_well_typed P pc c))).
idtac "Assumptions:".
Abort.
Print Assumptions ts_typechecker_complete.
Goal True.
idtac " ".

idtac "-------------------  not_ts_non_termination_com  --------------------".
idtac " ".

idtac "#> not_ts_non_termination_com".
idtac "Possible points: 1".
check_type @not_ts_non_termination_com (
(not (ts_well_typed xpub public termination_leak))).
idtac "Assumptions:".
Abort.
Print Assumptions not_ts_non_termination_com.
Goal True.
idtac " ".

idtac "-------------------  cf_well_typed_ts_cf_secure  --------------------".
idtac " ".

idtac "#> cf_well_typed_ts_cf_secure".
idtac "Possible points: 6".
check_type @cf_well_typed_ts_cf_secure (
(forall (P : pub_vars) (c : com) (_ : cf_well_typed P c), ts_cf_secure P c)).
idtac "Assumptions:".
Abort.
Print Assumptions cf_well_typed_ts_cf_secure.
Goal True.
idtac " ".

idtac "-------------------  public_outputs  --------------------".
idtac " ".

idtac "#> OUTPUT.oni_typechecker_sound".
idtac "Possible points: 0.5".
check_type @OUTPUT.oni_typechecker_sound (
(forall (P : pub_vars) (pc : label) (c : OUTPUT.com)
   (_ : @eq bool (OUTPUT.oni_typechecker P pc c) true),
 OUTPUT.oni_well_typed P pc c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_typechecker_sound.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_typechecker_complete".
idtac "Possible points: 0.5".
check_type @OUTPUT.oni_typechecker_complete (
(forall (P : pub_vars) (pc : label) (c : OUTPUT.com)
   (_ : @eq bool (OUTPUT.oni_typechecker P pc c) false),
 not (OUTPUT.oni_well_typed P pc c))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_typechecker_complete.
Goal True.
idtac " ".

idtac "#> OUTPUT.not_ni_wt_output1".
idtac "Possible points: 0.5".
check_type @OUTPUT.not_ni_wt_output1 (
(not (OUTPUT.oni_well_typed xpub public OUTPUT.output_insecure_com1))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.not_ni_wt_output1.
Goal True.
idtac " ".

idtac "#> OUTPUT.not_ni_wt_output2".
idtac "Possible points: 0.5".
check_type @OUTPUT.not_ni_wt_output2 (
(not (OUTPUT.oni_well_typed xpub public OUTPUT.output_insecure_com2))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.not_ni_wt_output2.
Goal True.
idtac " ".

idtac "#> OUTPUT.weaken_pc".
idtac "Possible points: 1".
check_type @OUTPUT.weaken_pc (
(forall (P : pub_vars) (pc1 pc2 : label) (c : OUTPUT.com)
   (_ : OUTPUT.oni_well_typed P pc1 c) (_ : @eq bool (can_flow pc2 pc1) true),
 OUTPUT.oni_well_typed P pc2 c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.weaken_pc.
Goal True.
idtac " ".

idtac "#> OUTPUT.secret_run_no_output".
idtac "Possible points: 2".
check_type @OUTPUT.secret_run_no_output (
(forall (P : pub_vars) (c : OUTPUT.com) (s s' : state)
   (os : OUTPUT.outputs) (_ : OUTPUT.oni_well_typed P secret c)
   (_ : OUTPUT.oceval c s s' os),
 @eq OUTPUT.outputs os (@nil nat))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.secret_run_no_output.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_well_typed_noninterferent".
idtac "Possible points: 2".
check_type @OUTPUT.oni_well_typed_noninterferent (
(forall (P : pub_vars) (c : OUTPUT.com)
   (_ : OUTPUT.oni_well_typed P public c),
 OUTPUT.noninterferent P c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_well_typed_noninterferent.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_well_typed_output_secure".
idtac "Possible points: 3".
check_type @OUTPUT.oni_well_typed_output_secure (
(forall (P : pub_vars) (c : OUTPUT.com)
   (_ : OUTPUT.oni_well_typed P public c),
 OUTPUT.output_secure P c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_well_typed_output_secure.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 24".
idtac "Max points - advanced: 24".
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
idtac "---------- not_cf_wt_noninterferent_com ---------".
Print Assumptions not_cf_wt_noninterferent_com.
idtac "---------- ts_typechecker ---------".
Print Assumptions ts_typechecker.
idtac "---------- ts_typechecker_sound ---------".
Print Assumptions ts_typechecker_sound.
idtac "---------- ts_typechecker_complete ---------".
Print Assumptions ts_typechecker_complete.
idtac "---------- not_ts_non_termination_com ---------".
Print Assumptions not_ts_non_termination_com.
idtac "---------- cf_well_typed_ts_cf_secure ---------".
Print Assumptions cf_well_typed_ts_cf_secure.
idtac "---------- OUTPUT.oni_typechecker_sound ---------".
Print Assumptions OUTPUT.oni_typechecker_sound.
idtac "---------- OUTPUT.oni_typechecker_complete ---------".
Print Assumptions OUTPUT.oni_typechecker_complete.
idtac "---------- OUTPUT.not_ni_wt_output1 ---------".
Print Assumptions OUTPUT.not_ni_wt_output1.
idtac "---------- OUTPUT.not_ni_wt_output2 ---------".
Print Assumptions OUTPUT.not_ni_wt_output2.
idtac "---------- OUTPUT.weaken_pc ---------".
Print Assumptions OUTPUT.weaken_pc.
idtac "---------- OUTPUT.secret_run_no_output ---------".
Print Assumptions OUTPUT.secret_run_no_output.
idtac "---------- OUTPUT.oni_well_typed_noninterferent ---------".
Print Assumptions OUTPUT.oni_well_typed_noninterferent.
idtac "---------- OUTPUT.oni_well_typed_output_secure ---------".
Print Assumptions OUTPUT.oni_well_typed_output_secure.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-01-07 13:38 *)

(* 2026-01-07 13:38 *)
