(** * SpecCT: Cryptographic Constant-Time and Speculative Constant-Time *)



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(** This chapter starts by presenting the cryptographic constant-time (CCT)
    discipline, which we statically enforce using a simple type system. This
    static discipline is, however, not enough to protect cryptographic programs
    against speculative execution attacks. To secure CCT programs against this
    more powerful attacker model we additionally use a program transformation
    called _Speculative Load Hardening_ (SLH). We prove formally that CCT
    programs protected by SLH achieve speculative constant-time security. *)

(* ################################################################# *)
(** * Cryptographic constant-time *)

(** Cryptographic constant-time (CCT) is a software countermeasure against
    timing side-channel attacks that is widely deployed for cryptographic
    implementations, for instance to prevent leakage of crypto keys
    [Barthe et al 2019] (in Bib.v).

    More generally, each program input has to be identified as public or secret,
    and intuitively the execution time of the program should not depend on
    secret inputs, even on processors with instruction and data caches.

    We, however, do not want to explicitly model execution time or caches, since
    - it would be very hard to do right, and
    - it would bring in too many extremely low-level details of the concrete compiler
      (Clang/LLVM 20.1.6) and hardware microarchitecture (Intel Core i7-8650U). *)

(** Instead CCT works with a _more abstract model of leakage_,
    which simply assumes that:
    - _all branches the program takes are leaked_;
      - since the path the program takes can greatly
        influence how long execution takes
      - this is exactly like in the Control Flow (CF)
        security model from [StaticIFC]
    - _all accessed memory addresses are leaked_;
      - since timing attacks can also exploit the latency difference between
        hits and misses in the data cache
    - _the operands influencing timing of variable-time operations are leaked_;
      - as an exercise we will add a division operation that leaks both operands.
*)

(** To ensure security against this leakage model, the CCT discipline requires that:

    - _the control flow of the program does not depend on secrets_;
      - intuitively this prevents the execution time of different program paths
        from directly depending on secrets:

        if Wsecret then ... slow computation ... else skip

    - _the accessed memory addresses do not depend on secrets_;
      - intuitively this prevents secrets from leaking into the data cache:

        Vsecret <- AP[Wsecret]

    - _the operands leaked by variable-time operations do not depend on secrets_.
      - this prevents leaking information about secrets e.g., via division:

        Usecret := div Vsecret Wsecret
*)

(** To model memory accesses that depend on secrets we will make the Imp
    language more realistic by adding arrays. *)

(** We need such an extension, since
    otherwise variable accesses in the original Imp map to memory operations at
    constant locations, which thus cannot depend on secrets, so in Imp CCT
    trivially holds for all CF well-typed programs. Array indices on the other
    hand are computed at runtime, which leads to accessing memory addresses that
    can depend on secrets, making CCT non-trivial for Imp with arrays.

    For instance, here is a simple program that is CF secure (since it does no
    branches), but not CCT secure (since it accesses memory based on secret
    information):
    - [Vsecret <- A[Wsecret] ] *)

(* ================================================================= *)
(** ** Adding constant-time conditional and refactoring expressions *)

(** But first, we add a [b ? e1 : e2] conditional expression that executes in
    constant time (for instance by being compiled to a special constant-time
    conditional move instruction). This constant-time conditional will also be
    used in our SLH countermeasure below. *)

(** Technically, adding such conditionals to Imp arithmetic expressions would
    make them dependent on boolean expressions. But boolean expressions are
    already dependent on arithmetic expressions. *)

(** To avoid making the definitions of arithmetic and boolean expressions
    mutually inductive, we drop boolean expressions altogether and encode them
    using arithmetic expressions. Our encoding of bools in terms of nats is
    similar to that of C, where zero means false, and non-zero means true. *)

(** We also refactor the semantics of binary operators in terms of the
    [binop] enumeration below, to avoid the duplication in Imp: *)

Inductive binop : Type :=
  | BinPlus
  | BinMinus
  | BinMult
  | BinEq
  | BinLe
  | BinAnd
  | BinImpl.

(** We define the semantics of [binop]s directly on nats. We are careful to
    allow other representations of true (any non-zero number).  *)

Definition not_zero (n : nat) : bool := negb (n =? 0).
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition eval_binop (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => bool_to_nat (n1 =? n2)
  | BinLe => bool_to_nat (n1 <=? n2)
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp) (* <--- REFACTORED *)
  | ACTIf (b : exp) (e1 e2 : exp). (* <--- NEW *)

(** We encode all the previous arithmetic and boolean operations: *)

Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr e1 e2 := BImpl (BNot e1) e2.
Definition BEq := ABin BinEq.
Definition BNeq e1 e2 := BNot (BEq e1 e2).
Definition BLe := ABin BinLe.
Definition BGt e1 e2 := BNot (BLe e1 e2).
Definition BLt e1 e2 := BGt e2 e1.

Hint Unfold eval_binop : core.
Hint Unfold APlus AMinus AMult : core.
Hint Unfold BTrue BFalse : core.
Hint Unfold BAnd BImpl BNot BOr BEq BNeq BLe BGt BLt : core.

(** The notations we use for expressions are the same as in Imp,
    except the notation for [be?e1:e2] which is new: *)
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2) (* <-- NEW *)
                 (in custom com at level 20, no associativity).

(* ================================================================= *)
(** ** Adding arrays *)

(** Now back to adding array loads and stores to commands: *)

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (e : exp)
  | Seq (c1 c2 : com)
  | If (be : exp) (c1 c2 : com)
  | While (be : exp) (c : com)
  | ALoad (x : string) (a : string) (i : exp) (* <--- NEW *)
  | AStore (a : string) (i : exp) (e : exp)  (* <--- NEW *).


Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.

Notation "x '<-' a '[[' i ']]'" := (ALoad x a i) (* <--- NEW *)
     (in custom com at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  := (AStore a i e) (* <--- NEW *)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com_scope.

Definition state := total_map nat.
Definition mem := total_map (list nat). (* <--- NEW *)

Fixpoint eval (st : state) (e: exp) : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | ABin b e1 e2 => eval_binop b (eval st e1) (eval st e2)
  | <{b ? e1 : e2}> => if not_zero (eval st b) then eval st e1
                           (* ^- NEW -> *)      else eval st e2
  end.

(** A couple of obvious lemmas that will be useful in the proofs: *)

Lemma not_zero_eval_S : forall b n st,
  eval st b = S n ->
  not_zero (eval st b) = true.
Proof. intros b n st H. rewrite H. reflexivity. Qed.

Lemma not_zero_eval_O : forall b st,
  eval st b = O ->
  not_zero (eval st b) = false.
Proof. intros b st H. rewrite H. reflexivity. Qed.

(** We also define an array update operation, to be used in the semantics of
    array stores below: *)

Fixpoint upd (i:nat) (ns:list nat) (n:nat) : list nat :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', n' :: ns' => n' :: upd i' ns' n
  | _, _ => ns
  end.

(* ================================================================= *)
(** ** Instrumenting semantics with observations *)

(** In addition to the boolean branches, which are observable in the CF security
    model, for CCT security also the index of array loads and stores are
    observable: *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OALoad (a : string) (i : nat)
  | OAStore (a : string) (i : nat).

Definition obs := list observation.

(** We define an instrumented big-step operational semantics producing these
    observations:
    - [<(st, m)> =[ c ]=> <(st', m', os)>]

    Intuitively, variables act like registers (not observable),
    while arrays act like the memory (addresses observable). *)

(**

          ---------------------------------------     (CTE_Skip)
          <(st, m)> =[ skip ]=> <(st, m, [])>

                          eval st e = n
      --------------------------------------------------    (CTE_Asgn)
      <(st, m)> =[ x := e ]=> <(x !-> n; st, m, [])>

            <(st, m)> =[ c1 ]=> <(st', m', os1)>
            <(st', m')> =[ c2 ]=> <(st'', m'', os2)>
      -----------------------------------------------------   (CTE_Seq)
      <(st, m)>  =[ c1 ; c2 ]=> <(st'', m'', os1 ++ os2)>

       let c := if not_zero (eval st be) then c1 else c2 in
            <(st,m)> =[ c ]=> <(st',m',os1)>
 ---------------------------------------------------------- (CTE_If)
  <(st, m)> =[ if be then c1 else c2 end]=>
   <(st', m', [OBranch (not_zero (eval st be))] ++ os1)>

<(st,m)> =[ if be then c; while be do c end else skip end ]=> <(st',m',os)>
------------------------------------------------------------------------------- (CTE_While)
            <(st,m)> =[ while be do c end ]=> <(st', m', os)>

              eval st ie = i              i < length (m a)
---------------------------------------------------------------------------- (CTE_ALoad)
<(st,m)> =[ x <- a[[ie]] ]=> <(x!->nth i (m a) 0; st, m,[OALoad a i])>

   eval st e = n     eval st ie = i    i < length (m a)
---------------------------------------------------------------------------   (CTE_AStore)
<(st,m)> =[ a[ie] <- e ]=> <(st, a!->upd i (m a) n; m,[OAStore a i])>

*)

Reserved Notation
         "'<(' st , m ')>' '=[' c ']=>' '<(' stt , mt , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, m constr, stt constr, mt constr at next level).

Inductive cteval : com -> state -> mem -> state -> mem -> obs -> Prop :=
  | CTE_Skip : forall st m,
      <(st , m)> =[ skip ]=> <(st, m, [])>
  | CTE_Asgn  : forall st m e n x,
      eval st e = n ->
      <(st, m)> =[ x := e ]=> <(x !-> n; st, m, [])>
  | CTE_Seq : forall c1 c2 st m st' m' st'' m'' os1 os2,
      <(st, m)> =[ c1 ]=> <(st', m', os1)>  ->
      <(st', m')> =[ c2 ]=> <(st'', m'', os2)> ->
      <(st, m)>  =[ c1 ; c2 ]=> <(st'', m'', os1++os2)>
  | CTE_If : forall st m st' m' be c1 c2 os1,
      let c := if not_zero (eval st be) then c1 else c2 in
      <(st, m)> =[ c ]=> <(st', m', os1)> ->
      <(st, m)> =[ if be then c1 else c2 end]=>
      <(st', m', [OBranch (not_zero (eval st be))] ++ os1)>
  | CTE_While : forall b st m st' m' os c,
      <(st,m)> =[ if b then c; while b do c end else skip end ]=>
      <(st', m', os)> -> (* <^- Nice trick; from small-step semantics *)
      <(st,m)> =[ while b do c end ]=> <(st', m', os)>
  | CTE_ALoad : forall st m x a ie i,
      eval st ie = i ->
      i < length (m a) ->
      <(st, m)> =[ x <- a[[ie]] ]=> <(x !-> nth i (m a) 0; st, m, [OALoad a i])>
  | CTE_AStore : forall st m a ie i e n,
      eval st e = n ->
      eval st ie = i ->
      i < length (m a) ->
      <(st, m)> =[ a[ie] <- e ]=> <(st, a !-> upd i (m a) n; m, [OAStore a i])>

  where "<( st , m )> =[ c ]=> <( stt , mt , os )>" := (cteval c st m stt mt os).

Hint Constructors cteval : core.

(* ================================================================= *)
(** ** Constant-time security definition *)

Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.
Definition pub_arrs := total_map label.

Definition pub_equiv (P : total_map label) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, P x = true -> s1 x = s2 x.

Lemma pub_equiv_refl :
  forall {X:Type} (P : total_map label) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym :
  forall {X:Type} (P : total_map label) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof.
  unfold pub_equiv. intros X P s1 s2 H x Px.
  rewrite H; auto.
Qed.

Lemma pub_equiv_trans :
  forall {X:Type} (P : total_map label) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof.
  unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
  rewrite H12; try rewrite H23; auto.
Qed.

Lemma pub_equiv_update_secret :
  forall {X: Type} (P : total_map label) (s1 s2 : total_map X)
         (x: string) (e1 e2: X),
  pub_equiv P s1 s2 ->
  P x = secret ->
  pub_equiv P (x !-> e1; s1) (x !-> e2; s2).
Proof.
  unfold pub_equiv. intros X P s1 s2 x e H Pe Px y Py.
  destruct (String.eqb_spec x y) as [Hxy | Hxy]; subst.
  - rewrite Px in Py. discriminate.
  - repeat rewrite t_update_neq; auto.
Qed.

Lemma pub_equiv_update_public :
  forall {X: Type} (P : total_map label) (s1 s2 : total_map X)
         (x: string) {e1 e2: X},
  pub_equiv P s1 s2 ->
  e1 = e2 ->
  pub_equiv P (x !-> e1; s1) (x !-> e2; s2).
Proof.
  unfold pub_equiv. intros X P s1 s2 x e1 e2 H Eq y Py.
  destruct (String.eqb_spec x y) as [Hxy | Hxy]; subst.
  - repeat rewrite t_update_eq; auto.
  - repeat rewrite t_update_neq; auto.
Qed.

Definition cct_secure P PA c :=
  forall st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
    pub_equiv P st1 st2 ->
    pub_equiv PA m1 m2 ->
    <(st1, m1)> =[ c ]=> <(st1', m1', os1)> ->
    <(st2, m2)> =[ c ]=> <(st2', m2', os2)> ->
    os1 = os2.

(* ================================================================= *)
(** ** Example CF secure program that is not CCT secure *)

Definition cct_insecure_prog :=
   <{{ V <- AP[[W]] }}> .

(** Let's assume that [W] and [V] are secret variables.
    This program is trivially CF secure, because it does not branch at all.
    But it is not CCT secure. *)

(** This is proved below. We first define the public variables and arrays, which
    we will use in this kind of examples: *)

Definition XYZpub : pub_vars :=
  (X!-> public; Y!-> public; Z!-> public; __ !-> secret).
Definition APpub : pub_arrs :=
  (AP!-> public; __ !-> secret).

Lemma XYZpub_true : forall x, XYZpub x = true -> x = X \/ x = Y \/ x = Z.
Proof.
  unfold XYZpub. intros x Hxyz.
  destruct (String.eqb_spec x X); auto.
  rewrite t_update_neq in Hxyz; auto.
  destruct (String.eqb_spec x Y); auto.
  rewrite t_update_neq in Hxyz; auto.
  destruct (String.eqb_spec x Z); auto.
  rewrite t_update_neq in Hxyz; auto.
  rewrite t_apply_empty in Hxyz. discriminate.
Qed.

Lemma APpub_true : forall a, APpub a = true -> a = AP.
Proof.
  unfold APpub. intros a Ha.
  destruct (String.eqb_spec a AP); auto.
  rewrite t_update_neq in Ha; auto. discriminate Ha.
Qed.

Lemma XYZpubXYZ : forall x, x = X \/ x = Y \/ x = Z -> XYZpub x = true.
Proof.
  intros x Hx.
  destruct Hx as [HX | HYZ]; subst.
  - reflexivity.
  - destruct HYZ as [HY | HZ]; subst; reflexivity.
Qed.

Example cct_insecure_prog_is_not_cct_secure :
  ~ (cct_secure XYZpub APpub cct_insecure_prog).
Proof.
  unfold cct_secure, cct_insecure_prog; intros CTSEC.
  remember (W !-> 1; __ !-> 0) as st1.
  remember (W !-> 2; __ !-> 0) as st2.
  remember (AP !-> [1;2;3]; __ !-> []) as m.
  specialize (CTSEC st1 st2 m m).

  assert (Contra: [OALoad AP 1] = [OALoad AP 2]).
  { eapply CTSEC; subst.
    (* public variables equivalent *)
    - apply pub_equiv_update_secret; auto.
      apply pub_equiv_refl.
    (* public arrays equivalent *)
    - apply pub_equiv_refl.
    - eapply CTE_ALoad; simpl; auto.
    - eapply CTE_ALoad; simpl; auto. }

  discriminate.
Qed.

(** **** Exercise: 2 stars, standard (cct_insecure_prog'_is_not_cct_secure)

    Show that also the following program is not CCT secure. *)
Definition cct_insecure_prog' :=
   <{{ AS[W] <- 42 }}> .

Example cct_insecure_prog'_is_not_cct_secure :
  ~ (cct_secure XYZpub APpub cct_insecure_prog').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Type system for cryptographic constant-time programming *)

(** In our CCT type system, the label assigned to the result of a constant-time
    conditional expression simply joins the labels of the 3 involved expressions:

        P |- be \in l   P |- e1 \in l1    P |- e2 \in l2
        ------------------------------------------------- (T_CTIf)
             P |- be?e1:e2 \in join l (join l1 l2)

    The rules for the other expressions are standard, and a lot fewer
    because of our refactoring:

            -----------------   (T_Num)
            P |- n \in public

            ----------------   (T_Id)
            P |- X \in (P X)

       P |- e1 \in l1      P |- e2 \in l2
      -----------------------------------   (T_Bin)
       P |- (e1 `op` e2) \in (join l1 l2)
*)

Definition join (l1 l2 : label) : label := l1 && l2.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Lemma join_public_l : forall {l},
  join public l = l.
Proof. reflexivity. Qed.

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

Reserved Notation "P '|-' a \in l" (at level 40).

Inductive exp_has_label (P:pub_vars) : exp -> label -> Prop :=
  | T_Num : forall n,
       P |- (ANum n) \in public
  | T_Id : forall X,
       P |- (AId X) \in (P X)
  | T_Bin : forall op e1 l1 e2 l2,
       P |- e1 \in l1 ->
       P |- e2 \in l2 ->
       P |- (ABin op e1 e2) \in (join l1 l2)
  | T_CTIf : forall be l e1 l1 e2 l2,
       P |- be \in l ->
       P |- e1 \in l1 ->
       P |- e2 \in l2 ->
       P |- <{ be ? e1 : e2 }> \in (join l (join l1 l2))

where "P '|-' e '\in' l" := (exp_has_label P e l).

Hint Constructors exp_has_label : core.

Theorem noninterferent_exp : forall {P s1 s2 e},
  pub_equiv P s1 s2 ->
  P |- e \in public ->
  eval s1 e = eval s2 e.
Proof.
  intros P s1 s2 e Heq Ht. remember public as l.
  generalize dependent Heql.
  induction Ht; simpl; intros.
  - reflexivity.
  - eapply Heq; auto.
  - eapply join_public in Heql.
    destruct Heql as [HP1 HP2]. subst.
    rewrite IHHt1, IHHt2; reflexivity.
  - eapply join_public in Heql.
    destruct Heql as [HP HP']. subst.
    eapply join_public in HP'.
    destruct HP' as [HP1 HP2]. subst.
    rewrite IHHt1, IHHt2, IHHt3; reflexivity.
Qed.

(** All rules for commands are exactly the same as for [cf_well_typed] (from
    [StaticIFC]), except [CCT_ALoad] and [CCT_AStore], which are new. *)

(**
                         ------------------                 (CCT_Skip)
                         P ;; PA |-ct- skip

             P |- e \in l    can_flow l (P X) = true
             -----------------------------------------      (CCT_Asgn)
                       P ;; PA |-ct- X := e

               P ;; PA |-ct- c1    P ;; PA |-ct- c2
               ------------------------------------          (CCT_Seq)
                       P ;; PA |-ct- c1;c2

  P |- be \in public    P ;; PA |-ct- c1    P ;; PA |-ct- c2
  ---------------------------------------------------------- (CCT_If)
               P ;; PA |-ct- if be then c1 else c2

                  P |- be \in public    P |-ct- c
                  ---------------------------------         (CCT_While)
                  P ;; PA |-ct- while be then c end

      P |- i \in public   can_flow (PA a) (P x) = true
      --------------------------------------------------   (CCT_ALoad)
                  P ;; PA |-ct- x <- a[[i]]

P |- i \in public   P |- e \in l   can_flow l (PA a) = true
--------------------------------------------------------------- (CCT_AStore)
                   P ;; PA |-ct- a[i] <- e
*)

Reserved Notation "P ';;' PA '|-ct-' c" (at level 40).

Inductive cct_well_typed (P:pub_vars) (PA:pub_arrs) : com -> Prop :=
  | CCT_Skip :
      P ;; PA |-ct- <{{ skip }}>
  | CCT_Asgn : forall X e l,
      P |- e \in l ->
      can_flow l (P X) = true ->
      P ;; PA |-ct- <{{ X := e }}>
  | CCT_Seq : forall c1 c2,
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ c1 ; c2 }}>
  | CCT_If : forall b c1 c2,
      P |- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ if b then c1 else c2 end }}>
  | CCT_While : forall b c1,
      P |- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- <{{ while b do c1 end }}>
  | CCT_ALoad : forall x a i,
      P |- i \in public ->
      can_flow (PA a) (P x) = true ->
      P ;; PA |-ct- <{{ x <- a[[i]] }}>
  | CCT_AStore : forall a i e l,
      P |- i \in public ->
      P |- e \in l ->
      can_flow l (PA a) = true ->
      P ;; PA |-ct- <{{ a[i] <- e }}>

where "P ;; PA '|-ct-' c" := (cct_well_typed P PA c).

Hint Constructors cct_well_typed : core.

(* ================================================================= *)
(** ** Exercise: CCT Type-Checker *)

(** In these exercises you will write a type-checker for the CCT type system
    above and prove your type-checker sound and complete. If you get stuck, you
    can take inspiration in the similar type-checkers from [StaticIFC]. *)

(** **** Exercise: 1 star, standard (label_of_exp) *)
Fixpoint label_of_exp (P:pub_vars) (e:exp) : label
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (label_of_exp_sound) *)
Lemma label_of_exp_sound : forall P e,
  P |- e \in label_of_exp P e.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (label_of_exp_unique) *)
Lemma label_of_exp_unique : forall P e l,
  P |- e \in l ->
  l = label_of_exp P e.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (cct_typechecker) *)
Fixpoint cct_typechecker (P PA:pub_vars) (c:com) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (cct_typechecker_sound) *)
Theorem cct_typechecker_sound : forall P PA c,
  cct_typechecker P PA c = true ->
  P ;; PA |-ct- c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (cct_typechecker_complete) *)
Theorem cct_typechecker_complete : forall P PA c,
  cct_typechecker P PA c = false ->
  ~ (P ;; PA |-ct- c).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we use the type-checker to show that the [cct_insecure_prog] and
    [cct_insecure_prog'] examples above are not well-typed. *)

Print cct_insecure_prog. (* <{{ X <- A[[W]] }}> *)
Print XYZpub. (* (X!-> public; Y!-> public; Z!-> public; __ !-> secret) *)
Print APpub. (* (AP!-> public; __ !-> secret) *)

(** **** Exercise: 1 star, standard (cct_insecure_prog_ill_typed) *)
Theorem cct_insecure_prog_ill_typed :
  ~(XYZpub ;; APpub |-ct- cct_insecure_prog).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (cct_insecure_prog'_ill_typed) *)
Theorem cct_insecure_prog'_ill_typed :
  ~(XYZpub ;; APpub |-ct- cct_insecure_prog').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Noninterference lemma *)

(** To prove the security of our type system, we first show a noninterference
    lemma, which is not that hard, given that our very restrictive type system
    ensures the two executions run in lock-step, since it disallows branching
    on secrets. *)

Lemma cct_well_typed_noninterferent :
  forall P PA c st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
  P ;; PA |-ct- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA m1 m2 ->
  <(st1, m1)> =[ c ]=> <(st1', m1', os1)> ->
  <(st2, m2)> =[ c ]=> <(st2', m2', os2)> ->
  pub_equiv P st1' st2' /\ pub_equiv PA m1' m2'.
Proof.
  intros P PA c st1 st2 m1 m2 st1' st2' m1' m2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1;
    intros os2' m2 Haeq m2' st2 Heq st2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  (* Most cases are similar as for [cf_well_typed] *)
  - split; auto.
  - split; auto. destruct l.
    + rewrite (noninterferent_exp Heq H10).
      eapply pub_equiv_update_public; auto.
    + simpl in H11. rewrite negb_true_iff in H11.
      eapply pub_equiv_update_secret; auto.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
    + subst c. destruct (eval st be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - (* NEW CASE: ALoad *)
    split; eauto.
    erewrite noninterferent_exp; eauto.
    destruct (PA a) eqn:PAa.
    + eapply pub_equiv_update_public; auto.
      eapply Haeq in PAa. rewrite PAa. reflexivity.
    + simpl in H15. rewrite negb_true_iff in H15.
      eapply pub_equiv_update_secret; auto.
  - (* NEW CASE: AStore *)
    split; eauto.
    destruct (PA a) eqn:PAa; simpl in *.
    + eapply Haeq in PAa. rewrite PAa.
      destruct l; [|discriminate].
      eapply pub_equiv_update_public; auto.
      repeat erewrite (noninterferent_exp Heq); auto.
    + eapply pub_equiv_update_secret; auto.
Qed.

(* ================================================================= *)
(** ** Final theorem: cryptographic constant-time security *)

Module Remember.
Definition cct_secure P PA c :=
  forall st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
    pub_equiv P st1 st2 ->
    pub_equiv PA m1 m2 ->
    <(st1, m1)> =[ c ]=> <(st1', m1', os1)> ->
    <(st2, m2)> =[ c ]=> <(st2', m2', os2)> ->
    os1 = os2.
End Remember.

Theorem cct_well_typed_secure : forall P PA c,
  P ;; PA |-ct- c ->
  cct_secure P PA c.
Proof.
  unfold cct_secure.
  intros P PA c Hwt st1 st2 m1 m2 st1' st2' m1' m2' os1 os2
    Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply cct_well_typed_noninterferent with (c:=c1); eauto.
    + eapply cct_well_typed_noninterferent with (c:=c1); eauto.
  - rewrite (noninterferent_exp Heq H11).
    f_equal; auto. eapply IHHeval1; eauto.
    + subst c. destruct (eval st be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - (* NEW CASE: ALoad *)
    f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* NEW CASE: AStore *)
    f_equal. f_equal. eapply noninterferent_exp; eassumption.
Qed.

(** Most cases of this proof are similar to the security proof for
    [cf_well_typed] from [StaticIFC]. In particular, [noninterference] is
    used to prove the sequence case in both proofs.

    The only new cases here are for array operations, and they follow
    immediately from [noninterferent_exp], since the CCT type system requires
    array indices to be public. *)

(* ================================================================= *)
(** ** Exercise: Adding division (non-constant-time operation) *)

(** The CCT discipline also prevents passing secrets to operations that are not
    constant time. For instance, division often takes time that depends on the
    values of the two operands. In this exercise we will add a new
    [x := e1 div e2] command for division, add corresponding evaluation and
    typing rules, and extend the security proofs with the new division case. *)

Module Div.

Inductive com : Type :=
| Skip
| Asgn (x : string) (e : exp)
| Seq (c1 c2 : com)
| If (be : exp) (c1 c2 : com)
| While (be : exp) (c : com)
| ALoad (x : string) (a : string) (i : exp)
| AStore (a : string) (i : exp) (e : exp)
| Div (x: string) (e1 e2: exp). (* <--- NEW *)

Open Scope com_scope.

(** Notations for the old commands are the same as before: *)
Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.
Notation "x '<-' a '[[' i ']]'" := (ALoad x a i)
     (in custom com at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  := (AStore a i e)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com_scope.

(** Notation for division: *)
Notation "x := y 'div' z" := (* <--- NEW *)
  (Div x y z)
    (in custom com at level 0, x constr at level 0,
        y custom com at level 85, z custom com at level 85, no associativity) : com_scope.

Inductive observation : Type :=
| OBranch (b : bool)
| OALoad (a : string) (i : nat)
| OAStore (a : string) (i : nat)
| ODiv (n1 n2: nat). (* <--- NEW *)

Definition obs := list observation.

(** We add a new rule to the big-step operational semantics that produces an
    [ODiv] observation:

               eval st e1 = n1     eval st e2 = n2
------------------------------------------------------------------ (CTE_Div)
<(st,m)> =[x := e1 div e2]=> <(x!->(n1/n2);st,m,[ODiv n1 n2])>

   Formally this looks as follows:
*)

Reserved Notation
         "'<(' st , m ')>' '=[' c ']=>' '<(' stt , mt , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, m constr, stt constr, mt constr at next level).

Inductive cteval : com -> state -> mem -> state -> mem -> obs -> Prop :=
  | CTE_Skip : forall st m,
      <(st , m)> =[ skip ]=> <(st, m, [])>
  | CTE_Asgn  : forall st m e n x,
      eval st e = n ->
      <(st, m)> =[ x := e ]=> <(x !-> n; st, m, [])>
  | CTE_Seq : forall c1 c2 st m st' m' st'' m'' os1 os2,
      <(st, m)> =[ c1 ]=> <(st', m', os1)>  ->
      <(st', m')> =[ c2 ]=> <(st'', m'', os2)> ->
      <(st, m)>  =[ c1 ; c2 ]=> <(st'', m'', os1++os2)>
  | CTE_If : forall st m st' m' be c1 c2 os1,
      let c := if not_zero (eval st be) then c1 else c2 in
      <(st, m)> =[ c ]=> <(st', m', os1)> ->
      <(st, m)> =[ if be then c1 else c2 end]=>
      <(st', m', [OBranch (not_zero (eval st be))] ++ os1)>
  | CTE_While : forall b st m st' m' os c,
      <(st,m)> =[ if b then c; while b do c end else skip end ]=>
      <(st', m', os)> ->
      <(st,m)> =[ while b do c end ]=> <(st', m', os)>
  | CTE_ALoad : forall st m x a ie i,
      eval st ie = i ->
      i < length (m a) ->
      <(st, m)> =[ x <- a[[ie]] ]=> <(x !-> nth i (m a) 0; st, m, [OALoad a i])>
  | CTE_AStore : forall st m a ie i e n,
      eval st e = n ->
      eval st ie = i ->
      i < length (m a) ->
      <(st, m)> =[ a[ie] <- e ]=> <(st, a !-> upd i (m a) n; m, [OAStore a i])>
  | CTE_Div : forall st m e1 n1 e2 n2 x, (* <--- NEW *)
      eval st e1 = n1 ->
      eval st e2 = n2 ->
      <(st, m)> =[ x := e1 div e2  ]=> <(x !-> (n1 / n2)%nat; st, m, [ODiv n1 n2] )>

  where "<( st , m )> =[ c ]=> <( stt , mt , os )>" := (cteval c st m stt mt os).

Hint Constructors cteval : core.

Reserved Notation "P ';;' PA '|-ct-' c" (at level 40).

(** **** Exercise: 1 star, standard (cct_well_typed_div)

    Add a new typing rule for division to [cct_well_typed] below.
    Your rule should prevent leaking secret division operands via observations. *)

Inductive cct_well_typed (P:pub_vars) (PA:pub_arrs) : com -> Prop :=
  | CCT_Skip :
      P ;; PA |-ct- <{{ skip }}>
  | CCT_Asgn : forall X e l,
      P |- e \in l ->
      can_flow l (P X) = true ->
      P ;; PA |-ct- <{{ X := e }}>
  | CCT_Seq : forall c1 c2,
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ c1 ; c2 }}>
  | CCT_If : forall b c1 c2,
      P |- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ if b then c1 else c2 end }}>
  | CCT_While : forall b c1,
      P |- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- <{{ while b do c1 end }}>
  | CCT_ALoad : forall x a i,
      P |- i \in public ->
      can_flow (PA a) (P x) = true ->
      P ;; PA |-ct- <{{ x <- a[[i]] }}>
  | CCT_AStore : forall a i e l,
      P |- i \in public ->
      P |- e \in l ->
      can_flow l (PA a) = true ->
      P ;; PA |-ct- <{{ a[i] <- e }}>
(* FILL IN HERE *)
   (* <--- Add your new typing rule here *)
  where "P ;; PA '|-ct-' c" := (cct_well_typed P PA c).
(* Do not modify the following line: *)
Definition manual_grade_for_cct_well_typed_div : option (nat*string) := None.
(** [] *)

Hint Constructors cct_well_typed : core.

(** **** Exercise: 2 stars, standard (cct_well_typed_div_noninterferent) *)
Theorem cct_well_typed_div_noninterferent :
  forall P PA c st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
  P ;; PA |-ct- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA m1 m2 ->
  <(st1, m1)> =[ c ]=> <(st1', m1', os1)> ->
  <(st2, m2)> =[ c ]=> <(st2', m2', os2)> ->
  pub_equiv P st1' st2' /\ pub_equiv PA m1' m2'.
Proof.
  intros P PA c st1 st2 m1 m2 st1' st2' m1' m2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1;
    intros os2' m2 Haeq m2' st2 Heq st2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - split; auto.
  - split; auto. destruct l.
    + rewrite (noninterferent_exp Heq H10).
      eapply pub_equiv_update_public; auto.
    + simpl in H11. rewrite negb_true_iff in H11.
      eapply pub_equiv_update_secret; auto.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
    + subst c. destruct (eval st be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - split; eauto.
    erewrite noninterferent_exp; eauto.
    destruct (PA a) eqn:PAa.
    + eapply pub_equiv_update_public; auto.
      eapply Haeq in PAa. rewrite PAa. reflexivity.
    + simpl in H15. rewrite negb_true_iff in H15.
      eapply pub_equiv_update_secret; auto.
  - split; eauto.
    destruct (PA a) eqn:PAa; simpl in *.
    + eapply Haeq in PAa. rewrite PAa.
      destruct l; [|discriminate].
      eapply pub_equiv_update_public; auto.
      repeat erewrite (noninterferent_exp Heq); auto.
    + eapply pub_equiv_update_secret; auto.
(* FILL IN HERE *) Admitted.
(** [] *)

(** We need to redefine [cct_secure] for our new command definition *)
Definition cct_secure P PA c :=
  forall st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
    pub_equiv P st1 st2 ->
    pub_equiv PA m1 m2 ->
    <(st1, m1)> =[ c ]=> <(st1', m1', os1)> ->
    <(st2, m2)> =[ c ]=> <(st2', m2', os2)> ->
    os1 = os2.

(** **** Exercise: 2 stars, standard (cct_well_typed_div_secure)

    Reprove CCT security of the type system. Hint: If this proof doesn't go
    through easily, you may need to go back and fix your div rule. *)
Theorem cct_well_typed_div_secure : forall P PA c,
  P ;; PA |-ct- c ->
  cct_secure P PA c.
Proof.
  unfold cct_secure.
  intros P PA c Hwt st1 st2 m1 m2 st1' st2' m1' m2' os1 os2
    Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply cct_well_typed_div_noninterferent with (c:=c1); eauto.
    + eapply cct_well_typed_div_noninterferent with (c:=c1); eauto.
  - rewrite (noninterferent_exp Heq H11).
    f_equal; auto. eapply IHHeval1; eauto.
    + subst c. destruct (eval st be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - f_equal. f_equal. eapply noninterferent_exp; eassumption.
  (* FILL IN HERE *) Admitted.
(** [] *)
End Div.

(* ################################################################# *)
(** * Speculative constant-time (text under development) *)

(** This second part of the chapter is based on the Spectre
    Declassified paper [Shivakumar et al 2023] (in Bib.v) in simplified form
    (e.g., without declassification). Like in this paper, we only look
    at a class of speculative execution attacks called Spectre v1. *)

(** The Rocq development below is complete, but the text about it is still under
    development and gets sparse after the first 3-4 subsections, especially for
    the security proof. Readers can skip the security proof, or if they have
    access to the slides associated to this chapter (i.e. the TERSE version)
    look there for a high-level overview of the security proof. *)

(* ================================================================= *)
(** ** CCT programs can be insecure under speculative execution *)

(** All variables mentioned in the program below ([X], [Y], [AP]) are _public_,
    so this program respects the CCT discipline, yet this program is not secure
    under speculative execution. *)

(** The size of public array [AP] is [3] and we check we're in bounds, yet this
    check can misspeculate! *)

Definition spec_insecure_prog :=
  <{{ if Y < 3 then (* <- this check can misspeculate for Y >= 3! *)
        X <- AP[[Y]]; (* <- speculative out of bounds access
                            loads _a secret_ to public variable X *)
        if X <= 5 then X := 5 else skip end (* <- speculatively leak X *)
      else skip end }}> .

Example spec_insecure_prog_is_ct_well_typed :
  XYZpub ;; APpub |-ct- spec_insecure_prog.
Proof.
  unfold spec_insecure_prog.
  - apply CCT_If; auto.
    + rewrite <- join_public_l.
      eapply T_Bin.
      * rewrite <- join_public_l.
        eapply T_Bin; auto.
      * eapply T_Num.
    + eapply CCT_Seq.
      * eapply CCT_ALoad; auto.
      * eapply CCT_If; auto.
        { rewrite <- join_public_l.
          eapply T_Bin; auto. }
        { eapply CCT_Asgn; eauto. }
Qed.

(** Here is a more realistic version of this example: *)

Definition spec_insecure_prog_2 :=
  <{{ X := 0;
      Y := 0;
      while Y < 3 do
        Z <- AP[[Y]];
        X := X + Z;
        Y := Y + 1
      end;
      if X <= 5 then X := 5 else skip end }}> .

Example spec_insecure_prog_2_is_ct_well_typed :
  XYZpub ;; APpub |-ct- spec_insecure_prog_2.
Proof.
  apply CCT_Seq.
  - eapply CCT_Asgn; auto.
  - apply CCT_Seq.
    + eapply CCT_Asgn; auto.
    + eapply CCT_Seq.
      { apply CCT_While.
        - rewrite <- join_public_l.
          apply T_Bin; auto.
          + rewrite <- join_public_l.
            apply T_Bin; auto.
          + unfold BFalse. auto.
        - eapply CCT_Seq.
          + eapply CCT_ALoad; auto.
          + eapply CCT_Seq.
            * eapply CCT_Asgn with (l:= public).
              { rewrite <- join_public_l.
                eapply T_Bin; auto. }
              { reflexivity. }
            * eapply CCT_Asgn with (l:= public).
              { rewrite <- join_public_l.
                eapply T_Bin; auto. }
              { reflexivity. } }
      { apply CCT_If; auto.
        - rewrite <- join_public_l.
          eapply T_Bin; auto.
        - eapply CCT_Asgn; auto. }
Qed.

(** All variables mentioned in the program are again public, so also this
    program respects the CCT discipline, yet it is also not secure under
    speculative execution. *)

(** This example is formalized at the end of the chapter. *)

(* ================================================================= *)
(** ** Speculative semantics *)

(** To reason about the security of these examples against Spectre v1 we will
    introduce a speculative semantics. To model leakage the semantics uses the
    same CCT observations as above ([OBranch], [OALoad], and [OAStore]). *)

(** More interestingly, to model speculative execution we add to the semantics
    adversary-provided _directions_, which control the speculation behavior: *)

Inductive direction :=
| DStep  (* adversary chooses the correct branch of conditional *)
| DForce (* adversary forces us take the wrong branch of conditional *)
| DLoad (a : string) (i : nat)   (* for speculative OOB array accesses *)
| DStore (a : string) (i : nat). (* adversary chooses array and index *)

Definition dirs := list direction.

(** This gives us a very high-level model of speculation that abstracts away
    low-level details such as the compiler, branch predictors, memory layout,
    speculation window, rollbacks, etc. We do this in a way that tries to
    overapproximate the adversary's power.

    This kind of speculation model is actually used by the Jasmin language for
    high-assurance crypto. *)

(** Compared to the CCT semantics with observations as output, we now add the
    directions as input to the evaluation judgement and we also track a
    misspeculation bit [b]. *)

(**

  ----------------------------------------- (Spec_Skip)
  <(st,m,b,[])> =[skip]=> <(st,m,b,[])>

                 eval st e = n
   ----------------------------------------------- (Spec_Asgn)
   <(st,m,b,[])> =[x:=e]=> <(x!->n;st,m,b,[])>

     <(st,m,b,ds1)> =[c1]=> <(st',m',b',os1)>
   <(st',m',b',ds2)> =[c2]=> <(st'',m'',b'',os2)>
------------------------------------------------------------ (Spec_Seq)
<(st,m,b,ds1++ds2)> =[c1;c2]=> <(st'',m'',b'',os1++os2)>

  <(st,m,b,ds)> =[ if be then c; while be do c end ]=>
  <(st',m',b',os)>
----------------------------------------------------------- (Spec_While)
<(st,m,b,ds)> =[ while be do c end ]=> <(st',m',b',os)>

*)

(**
   let c := if not_zero (eval st be) then c1 else c2 in
       <(st,m,b,ds)> =[ c ]=> <(st',m',b',os1)>
 ---------------------------------------------------------- (Spec_If)
 <(st,m,b, DStep::ds)> =[ if be then c1 else c2 end ]=>
   <(st',m',b', [OBranch (not_zero (eval st be))]++os1)>

   let c := if not_zero (eval st be) then c2 else c1 in
     <(st,m,true,ds)> =[ c ]=> <(st',m',b',os1)>
---------------------------------------------------------- (Spec_If_F)
<(st,m,b, DForce::ds)> =[ if be then c1 else c2 end ]=>
  <(st',m',b', [OBranch (not_zero (eval st be))]++os1)>
*)

(**

      eval st ie = i      i < length(m a)
 ----------------------------------------------------- (Spec_ALoad)
 <(st, m, b, [DStep])> =[ x <- a[[ie]] ]=>
 <(x !-> nth i (m a) 0; st, m, b, [OALoad a i])>

eval st ie = i   i >= length(m a)   i' < length(m a')
------------------------------------------------------------ (Spec_ALoad_U)
  <(st, m, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
  <(x !-> nth i' (m a') 0; st, m, true, [OALoad a i])>

 eval st e = n    eval st ie = i    i < length(m a)
----------------------------------------------------------- (Spec_AStore)
    <(st, m, b, [DStep])> =[ a[ie] <- e ]=>
    <(st, a !-> upd i (m a) n; m, b, [OAStore a i])>

        eval st e = n     eval st ie = i
      i >= length(m a)   i' < length(m a')
----------------------------------------------------------- (Spec_AStore_U)
 <(st, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
 <(st, a' !-> upd i' (m a') n; m, true, [OAStore a i])>
*)

(** Formally this definition looks as follows: *)

Reserved Notation
  "'<(' st , m , b , ds ')>' '=[' c ']=>' '<(' stt , mt , bb , os ')>'"
  (at level 40, c custom com at level 99,
   st constr, m constr, stt constr, mt constr at next level).

Inductive spec_eval : com -> state -> mem -> bool -> dirs ->
                             state -> mem -> bool -> obs -> Prop :=
  | Spec_Skip : forall st m b,
      <(st, m, b, [])> =[ skip ]=> <(st, m, b, [])>
  | Spec_Asgn  : forall st m b e n x,
      eval st e = n ->
      <(st, m, b, [])> =[ x := e ]=> <(x !-> n; st, m, b, [])>
  | Spec_Seq : forall c1 c2 st m b st' m' b' st'' m'' b'' os1 os2 ds1 ds2,
      <(st, m, b, ds1)> =[ c1 ]=> <(st', m', b', os1)>  ->
      <(st', m', b', ds2)> =[ c2 ]=> <(st'', m'', b'', os2)> ->
      <(st, m, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', m'', b'', os1++os2)>
  | Spec_If : forall st m b st' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval st be)) then c1 else c2) in
      <(st, m, b, ds)> =[ c ]=> <(st', m', b', os1)> ->
      <(st, m, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
      <(st', m', b', [OBranch (not_zero (eval st be))] ++ os1)>
  | Spec_If_F : forall st m b st' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval st be)) then c2 else c1) in (* <-- branches swapped *)
      <(st, m, true, ds)> =[ c ]=> <(st', m', b', os1)> ->
      <(st, m, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
      <(st', m', b', [OBranch (not_zero (eval st be))] ++ os1)>
  | Spec_While : forall be st m b ds st' m' b' os c,
      <(st, m, b, ds)> =[ if be then c; while be do c end else skip end ]=>
      <(st', m', b', os)> ->
      <(st, m, b, ds)> =[ while be do c end ]=> <(st', m', b', os)>
  | Spec_ALoad : forall st m b x a ie i,
      eval st ie = i ->
      i < length (m a) ->
      <(st, m, b, [DStep])> =[ x <- a[[ie]] ]=>
      <(x !-> nth i (m a) 0; st, m, b, [OALoad a i])>
  | Spec_ALoad_U : forall st m x a ie i a' i',
      eval st ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      <(st, m, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
      <(x !-> nth i' (m a') 0; st, m, true, [OALoad a i])>
  | Spec_AStore : forall st m b a ie i e n,
      eval st e = n ->
      eval st ie = i ->
      i < length (m a) ->
      <(st, m, b, [DStep])> =[ a[ie] <- e ]=>
      <(st, a !-> upd i (m a) n; m, b, [OAStore a i])>
  | Spec_AStore_U : forall st m a ie i e n a' i',
      eval st e = n ->
      eval st ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      <(st, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
      <(st, a' !-> upd i' (m a') n; m, true, [OAStore a i])>

  where "<( st , m , b , ds )> =[ c ]=> <( stt , mt , bb , os )>" :=
    (spec_eval c st m b ds stt mt bb os).

Hint Constructors spec_eval : core.



(* ================================================================= *)
(** ** Speculative constant-time security definition *)

(** The definition of speculative constant-time security is very similar to CCT
    security, but applied to the speculative semantics. The two executions
    receive the same directions [ds]: *)

Definition spec_ct_secure P PA c :=
  forall st1 st2 m1 m2 st1' st2' m1' m2' b1' b2' os1 os2 ds,
    pub_equiv P st1 st2 ->
    pub_equiv PA m1 m2 ->
    <(st1, m1, false, ds)> =[ c ]=> <(st1', m1', b1', os1)> ->
    <(st2, m2, false, ds)> =[ c ]=> <(st2', m2', b2', os2)> ->
    os1 = os2.

(** We can use this definition to show that our first example is speculatively
    insecure: *)

Print spec_insecure_prog.
(* <{{ if Y < 3 then
         X <- AP [[Y]];
         if X <= 5 then X := 5 else skip end
       else skip end }}> *)

(** For this we build a counterexample where the attacker chooses an
    out-of-bounds index [Y = 3] and then passes the directions:
    [[DForce; DLoad AS 0; DStep]].  This causes the two executions to load
    different values for [X] from index [0] of secret array [AS].
    If the different values loaded from [AS[0]] are well chosen (e.g., [4 <= 5]
    in the first execution and [7 > 5] in the second) this causes two different
    observations: - [[OBranch false; OALoad AP 3; OBranch true]] and - [[OBranch
    false; OALoad AP 3; OBranch false]].  *)

Example spec_insecure_prog_is_spec_insecure :
  ~(spec_ct_secure XYZpub APpub spec_insecure_prog).
Proof.
  unfold spec_insecure_prog. intros Hcs.
  remember (Y!-> 3; __ !-> 0) as st.
  remember (AP!-> [0;1;2]; AS!-> [4;1]; __ !-> []) as m1.
  remember (AP!-> [0;1;2]; AS!-> [7;1]; __ !-> []) as m2.
  remember (DForce :: ([DLoad AS 0] ++ [DStep])) as ds.
  remember (([OBranch false] ++ ([OALoad AP 3]) ++ [OBranch true])) as os1.
  remember (([OBranch false] ++ ([OALoad AP 3])++ [OBranch false])) as os2.

  assert (Heval1:
            <(st, m1, false, ds )> =[ spec_insecure_prog ]=>
            <( X!-> 5; X!-> 4; st, m1, true, os1)>).
  { unfold spec_insecure_prog; subst.
    eapply Spec_If_F. eapply Spec_Seq.
    - eapply Spec_ALoad_U; simpl; eauto.
    - rewrite <- app_nil_l with (l:=[OBranch true]).
      eapply Spec_If; simpl. eapply Spec_Asgn; eauto. }

  assert (Heval2:
            <(st, m2, false, ds )> =[ spec_insecure_prog ]=>
            <( X!-> 7; st, m2, true, os2)>).
    { unfold spec_insecure_prog; subst.
      eapply Spec_If_F. eapply Spec_Seq.
      - eapply Spec_ALoad_U; simpl; eauto.
      - rewrite <- app_nil_l with (l:=[OBranch false]).
        eapply Spec_If; simpl. auto. }

  subst. eapply Hcs in Heval1.
  + eapply Heval1 in Heval2. inversion Heval2.
  + eapply pub_equiv_refl.
  + apply pub_equiv_update_public; auto.
    apply pub_equiv_update_secret; auto.
    apply pub_equiv_refl.
Qed.

(** **** Exercise: 1 star, standard (speculation_bit_monotonic) *)

(** As mentioned above, our speculative semantics is very high-level, and
    doesn't have to deal with detecting misspeculation and rolling back. So in
    our semantics once the misspeculation bit is set to true, it will stay set: *)

Lemma speculation_bit_monotonic :
  forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma speculation_needs_force :
  forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

(** We can recover sequential execution from [spec_eval] if there is no
    speculation, so all directives are [DStep] and misspeculation flag starts
    set to [false]. *)

Definition seq_spec_eval (c :com) (st :state) (m :mem)
    (st' :state) (m' :mem) (os :obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(st, m, false, ds)> =[ c ]=> <(st', m', false, os)>.

(* We prove that this new definition for sequential execution is equivalent to
   the old one, i.e. [cteval].  *)

Lemma cteval_equiv_seq_spec_eval : forall c st m st' m' os,
  seq_spec_eval c st m st' m' os <-> <(st, m)> =[ c ]=> <(st', m', os)>.
Proof.
  intros c st m st' m' os. unfold seq_spec_eval. split; intros H.
  - (* -> *)
    destruct H as [ds [Hstep Heval] ].
    induction Heval; try (now econstructor; eauto).
    + (* Spec_Seq *)
      eapply CTE_Seq.
      * eapply IHHeval1. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (left; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
      * eapply IHHeval2. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (right; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
    + (* Spec_If *)
      eapply CTE_If. destruct (eval st be) eqn:Eqbe.
      * eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn.
        apply Hstep in HdIn. assumption.
      * eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn.
        apply Hstep in HdIn. assumption.
    + (* Spec_IF_F; contra *)
      exfalso.
      assert (L: ~(DForce = DStep)) by discriminate.
      apply L. apply (Hstep DForce). apply in_eq.
    + (* Spec_ALoad_U; contra *)
      exfalso.
      assert (L: ~(DLoad a' i' = DStep)) by discriminate.
      apply L. apply (Hstep (DLoad a' i')). apply in_eq.
    + (* Spec_AStore_U; contra *)
      exfalso.
      assert (L: ~(DStore a' i' = DStep)) by discriminate.
      apply L. apply (Hstep (DStore a' i')). apply in_eq.
  - (* <- *)
    induction H.
    + (* CTE_Skip *)
      exists []; split; [| eapply Spec_Skip].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Asgn *)
      exists []; split; [| eapply Spec_Asgn; assumption].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Seq *)
      destruct IHcteval1 as [ds1 [Hds1 Heval1] ].
      destruct IHcteval2 as [ds2 [Hds2 Heval2] ].
      exists (ds1 ++ ds2). split; [| eapply Spec_Seq; eassumption].
      intros d HdIn. apply in_app_or in HdIn.
      destruct HdIn as [Hin1 | Hin2].
      * apply Hds1 in Hin1. assumption.
      * apply Hds2 in Hin2. assumption.
    + (* CTE_If *)
      destruct IHcteval as [ds [Hds Heval] ].
      exists (DStep :: ds). split.
      * intros d HdIn. apply in_inv in HdIn.
        destruct HdIn as [Heq | HIn];
          [symmetry; assumption | apply Hds; assumption].
      * subst c. eapply Spec_If. eauto.
    + (* CTE_While *)
      destruct IHcteval as [ds [Hds Heval] ].
      exists ds. split; [assumption |].
      eapply Spec_While; assumption.
    + (* CTE_ALoad *)
      exists [DStep]. split.
      * simpl. intros d HdIn.
        destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_ALoad; assumption.
    + (* CTE_AStore *)
      exists [DStep]. split.
      * simpl. intros d HdIn.
        destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_AStore; assumption.
Qed.

(** **** Exercise: 1 star, standard (ct_well_typed_seq_spec_eval_ct_secure) *)
Lemma ct_well_typed_seq_spec_eval_ct_secure :
  forall P PA c st1 st2 m1 m2 st1' st2' m1' m2' os1 os2,
  P ;; PA |-ct- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA m1 m2 ->
  seq_spec_eval c st1 m1 st1' m1' os1 ->
  seq_spec_eval c st2 m2 st2' m2' os2 ->
  os1 = os2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Selective SLH transformation *)

(** Now how can we make CCT programs secure against speculative execution
    attacks? It turns out that we can protect such programs against Spectre v1
    by doing only two things:
    - Keep track of a misspeculation flag using constant-time conditionals;
    - Use this flag to mask the value of misspeculated public loads.

    We implement this as a _Selective Speculative Load Hardening_ (SLH)
    transformation that we will show enforces speculative constant-time security
    for all CCT programs.

    This SLH transformation is "selective", since it only masks _public_ loads.
    A non-selective SLH transformation was invented in LLVM, but what they
    implement is anyway much more complicated. *)

Definition msf : string := "msf".

Fixpoint sel_slh (P:pub_vars) (c:com) :=
  match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{sel_slh P c1; sel_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then msf := (be ? msf : 1); sel_slh P c1
               else msf := (be ? 1 : msf); sel_slh P c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be do msf := (be ? msf : 1); sel_slh P c end;
         msf := (be ? 1 : msf)}}>
  | <{{x <- a[[i]]}}> =>
      if P x then <{{x <- a[[i]]; x := (msf <> 0) ? 0 : x}}>
             else <{{x <- a[[i]]}}>
  | <{{a[i] <- e}}> => <{{a[i] <- e}}>
  end.

Print spec_insecure_prog.
(* <{{ if Y < 3 then
         X <- AP [[Y]];
         if X <= 5 then X := 5 else skip end
       else skip end }}> *)

Definition sel_slh_spec_insecure_prog :=
<{{ if Y < 3 then
      msf := ((Y < 3) ? msf : 1);
      (X <- AP[[Y]]; X := (msf <> 0) ? 0 : X);
      if X <= 5 then
        msf := ((X <= 5) ? msf : 1);
        X := 5
      else msf := ((X <= 5) ? 1 : msf); skip end
    else msf := ((Y < 3) ? 1 : msf); skip end }}>.

Lemma sel_slh_spec_insecure_prog_check:
  sel_slh XYZpub spec_insecure_prog = sel_slh_spec_insecure_prog.
Proof. reflexivity. Qed.

(** When misspeculation occurs in the first condition [if Z < 1], the
    transformation detects this misspeculation and sets [msf] (misspeculation
    flag) to [1].  Then, although the secret value gets loaded into X via the
    out-of-bounds access [X <- AP[[Z]]], it is immediatly overwritten with 0 due
    to the masking code [X := (msf <> 0) ? 0 : X] that follows. As a result, all
    subsequent operations like [if X <= 5] only uses the masked value [0]
    instead of the actual secret. *)

(* ================================================================= *)
(** ** Main proof idea: use compiler correctness wrt ideal semantics *)

(** To prove this transformation secure, Spectre Declassified uses an ideal
    semantics, capturing selective speculative load hardening more abstractly.
    The proof effort is decomposed into:
    - a speculative constant-time proof for the ideal semantics;
    - a compiler correctness proof for the [sel_slh] transformation, taking source
      programs which are executed using the ideal semantics, to target programs
      executed using the speculative semantics.
 *)

(** In a little bit more detail, we're intuitively trying to prove:

forall P PA c, P;;PA |-ct- c -> spec_ct_secure P PA (sel_slh P c),

    where the conclusion looks as follows:
<<
forall st1 st2 m1 m2 st1' st2' m1' m2' b1' b2' os1 os2 ds,
  pub_equiv P st1 st2 ->
  pub_equiv PA m1 m2 ->
  <(st1,m1,false,ds)> =[ sel_slh P c ]=> <(st1',m1',b1',os1)> ->
  <(st2,m2,false,ds)> =[ sel_slh P c ]=> <(st2',m2',b2',os2)> ->
  os1 = os2

    Compiler correctness allows us to get rid of [sel_slh P c] in the premises
    and instead get an execution in terms of the ideal semantics:

  <(st,m,b,ds)> =[ sel_slh P c ]=> <(st',m',b',os)> ->
    P |-i <(st,m,b,ds)> =[ c ]=> <(msf!->st msf;st',m',b',os)>
*)

(** One thing to note is that the ideal semantics doesn't track misspeculation
    in the [msf] variable, but instead directly uses the misspeculation bit in
    the speculative semantics for masking. This allows us to keep the ideal
    semantics simple, and then we show that [msf] correctly tracks misspeculation
    in our compiler correctness proof . *)

(* ================================================================= *)
(** ** Ideal semantics definition *)

(** All rules of the ideal semantics are the same as for the speculative
    semantics, except the ones for array loads, which add the extra
    masking done by [sel_slh] on top of the speculative semantics.

      eval st ie = i      i < length(m a)
 ----------------------------------------------------- (Ideal_ALoad)
let v := if b && P x then 0 else nth i (m a) 0 in
P |-i <(st, m, b, [DStep])> =[ x <- a[[ie]] ]=>
      <(x !-> v; st, m, b, [OALoad a i])>

eval st ie = i   i >= length(m a)   i' < length(m a')
------------------------------------------------------------ (Ideal_ALoad_U)
let v := if P x then 0 else nth i' (m a') 0 in
P |-i <(st, m, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
      <(x !-> v; st, m, true, [OALoad a i])>
*)

Reserved Notation
  "P '|-i' '<(' st , m , b , ds ')>' '=[' c ']=>' '<(' stt , mt , bb , os ')>'"
  (at level 40, c custom com at level 99,
   st constr, m constr, stt constr, mt constr at next level).

Inductive ideal_eval (P:pub_vars) :
    com -> state -> mem -> bool -> dirs ->
           state -> mem -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st m b,
      P |-i <(st, m, b, [])> =[ skip ]=> <(st, m, b, [])>
  | Ideal_Asgn  : forall st m b e n x,
      eval st e = n ->
      P |-i <(st, m, b, [])> =[ x := e ]=> <(x !-> n; st, m, b, [])>
  | Ideal_Seq : forall c1 c2 st m b st' m' b' st'' m'' b'' os1 os2 ds1 ds2,
      P |-i <(st, m, b, ds1)> =[ c1 ]=> <(st', m', b', os1)>  ->
      P |-i <(st', m', b', ds2)> =[ c2 ]=> <(st'', m'', b'', os2)> ->
      P |-i <(st, m, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', m'', b'', os1++os2)>
  | Ideal_If : forall st m b st' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval st be)) then c1 else c2) in
      P |-i <(st, m, b, ds)> =[ c ]=> <(st', m', b', os1)> ->
      P |-i <(st, m, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', m', b', [OBranch (not_zero (eval st be))] ++ os1 )>
  | Ideal_If_F : forall st m b st' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval st be)) then c2 else c1) in (* <-- branches swapped *)
      P |-i <(st, m, true, ds)> =[ c ]=> <(st', m', b', os1)> ->
      P |-i <(st, m, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', m', b', [OBranch (not_zero (eval st be))] ++ os1)>
  | Ideal_While : forall be st m b ds st' m' b' os c,
      P |-i <(st, m, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', m', b', os)> ->
      P |-i <(st, m, b, ds)> =[ while be do c end ]=> <(st', m', b', os)>
  | Ideal_ALoad : forall st m b x a ie i,
      eval st ie = i ->
      i < length (m a) ->
      let v := if b && P x then 0 else nth i (m a) 0 in
      P |-i <(st, m, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> v; st, m, b, [OALoad a i])>
  | Ideal_ALoad_U : forall st m x a ie i a' i',
      eval st ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      let v := if P x then 0 else nth i' (m a') 0 in
      P |-i <(st, m, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> v; st, m, true, [OALoad a i])>
  | Ideal_AStore : forall st m b a ie i e n,
      eval st e = n ->
      eval st ie = i ->
      i < length (m a) ->
      P |-i <(st, m, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (m a) n; m, b, [OAStore a i])>
  | Ideal_AStore_U : forall st m a ie i e n a' i',
      eval st e = n ->
      eval st ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      P |-i <(st, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (m a') n; m, true, [OAStore a i])>

  where "P |-i <( st , m , b , ds )> =[ c ]=> <( stt , mt , bb , os )>" :=
    (ideal_eval P c st m b ds stt mt bb os).

Hint Constructors ideal_eval : core.

(* ================================================================= *)
(** ** Ideal semantics enforces speculative constant-time *)

(** Let's now prove that the ideal semantics does enforce speculative
    constant-time.  As in the proofs we did before for constant-time and CF
    security, we rely on a proof of noninterference. For our ideal semantics
    this noninterference proof requires interesting generalization of the
    induction hypothesis (see [ct_well_typed_ideal_noninterferent_general]). *)

(** Generalization 1: We need to also deal with executions ending with [b=true],
    but in that case we cannot ensure that the array states are publicly
    equivalent, since our selective SLH does not mask misspeculated stores (for
    efficiency, since it's not needed for security). This requires to generalize
    the [pub_equiv PA m1 m2] premise of our statements too. *)

(** Generalization 2: To show that the two executions run in lock-step the proof
    uses not only the CCT type system (not branching on secrets) but also the
    fact that the directions are the same, which we need to establish as an
    extra invariant though. *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H.
  - auto.
  - simpl in H; apply prefix_cons in H. apply IH in H. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof.
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

Ltac split4 := split; [|split; [| split] ].

Lemma ct_well_typed_ideal_noninterferent_general : forall P PA c,
  forall st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds1 ds2,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    (b = false -> pub_equiv PA m1 m2) -> (* Generalization 1 *)
    (prefix ds1 ds2 \/ prefix ds2 ds1) -> (* <- Generalization 2 *)
    P |-i <(st1, m1, b, ds1)> =[ c ]=> <(st1', m1', b1', os1)> ->
    P |-i <(st2, m2, b, ds2)> =[ c ]=> <(st2', m2', b2', os2)> ->
    pub_equiv P st1' st2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv PA m1' m2') /\ (* <- Generalization 1 *)
      ds1 = ds2.  (* <- Generalization 2 *)
Proof.
  intros P PA c st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds1 ds2
    Hwt Heq Haeq Hds Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2. generalize dependent b2'.
  generalize dependent ds2.
  induction Heval1; intros ds2X Hds b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) auto.
  - (* Asgn *) split4; auto.
    destruct (P x) eqn:EqPx.
    + eapply pub_equiv_update_public; eauto.
      eapply noninterferent_exp; eauto.
      destruct l; [auto | simpl in H14; discriminate].
    + eapply pub_equiv_update_secret; eauto.
  - (* Seq *)
    destruct Hds as [Hpre | Hpre]; apply prefix_app in Hpre as Hds1.
    + (* prefix (ds1 ++ ds2) (ds0 ++ ds3) *)
      eapply IHHeval1_1 in Hds1; eauto.
      destruct Hds1 as [ Hstates [Hbits [Hmates Hdirections] ] ]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder. subst. reflexivity.
    + (* prefix (ds0 ++ ds3) (ds1 ++ ds2) *)
      eapply IHHeval1_1 with (ds2:=ds0) in H13; eauto; [| tauto].
      destruct H13 as [ Hstates [Hbits [Hmates Hdirections] ] ]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder; subst; reflexivity.
  - (* If *)
    remember (if not_zero (eval st be) then c1 else c2) as c5.
    assert(G : P ;; PA |-ct- c5).
    { subst c5. destruct (eval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    subst c4 c5. erewrite noninterferent_exp in H10.
    + specialize (IHHeval1 G _ Gds _ _ _ Haeq _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* IF; contra *)
    apply prefix_or_heads in Hds; inversion Hds.
  - (* IF; contra *)
     apply prefix_or_heads in Hds; inversion Hds.
  - (* If_F; analog to If *)
    remember (if not_zero (eval st be) then c2 else c1) as c5.
    assert(G : P ;; PA |-ct- c5).
    { subst c5. destruct (eval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    subst c4 c5. erewrite noninterferent_exp in H10.
    + assert(GG: true = false -> pub_equiv PA m a2). (* <- only difference *)
      { intro Hc. discriminate. }
      specialize (IHHeval1 G _ Gds _ _ _ GG _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* While *) eapply IHHeval1; try eassumption. repeat constructor; eassumption.
  - (* ALoad *) split4; eauto.
    destruct (P x) eqn:EqPx; simpl.
    + eapply pub_equiv_update_public; eauto.
      destruct b2' eqn:Eqb2'; simpl; [reflexivity |].
      unfold can_flow in H18. eapply orb_true_iff in H18.
      destruct H18 as [Hapub | Contra]; [| simpl in Contra; discriminate].
      subst v v1 v2. eapply Haeq in Hapub; [| reflexivity]. rewrite Hapub.
      eapply noninterferent_exp in Heq; eauto. rewrite Heq.
      reflexivity.
    + eapply pub_equiv_update_secret; eauto.
  - (* ALoad_U *)
    split4; eauto.
    + destruct (P x) eqn:EqPx.
      * simpl. eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* ALoad *)
    split4; eauto.
    + destruct (P x) eqn:EqPx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* ALoad_U *)
    split4; eauto.
    + destruct (P x) eqn:EqPx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
  - (* AStore *)
    split4; eauto. intro Hb2'.
    destruct (PA a) eqn:EqPAa.
    + eapply pub_equiv_update_public; eauto.
      destruct l eqn:Eql.
      * eapply noninterferent_exp in H19, H20; eauto. rewrite H19, H20.
        apply Haeq in Hb2'. apply Hb2' in EqPAa. rewrite EqPAa. reflexivity.
      * simpl in H21. discriminate.
    + eapply pub_equiv_update_secret; eauto.
  - (* AStore_U; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* AStore; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* AStore_U; contra *)
    split4; eauto.
    + intro contra. discriminate contra.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
Qed.

Corollary ct_well_typed_ideal_noninterferent :
  forall P PA c st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    (b = false -> pub_equiv PA m1 m2) ->
    P |-i <(st1, m1, b, ds)> =[ c ]=> <(st1', m1', b1', os1)> ->
    P |-i <(st2, m2, b, ds)> =[ c ]=> <(st2', m2', b2', os2)> ->
    pub_equiv P st1' st2' /\ b1' = b2' /\ (b1' = false -> pub_equiv PA m1' m2').
Proof.
  intros P PA c st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  eapply ct_well_typed_ideal_noninterferent_general in Heval2; eauto; try tauto.
  left. apply prefix_refl.
Qed.

(** This corollary (used below in the sequence case) also follows from
    [noninterferent_general] *)
Corollary aux : forall P PA st1 st2 m1 m2 b ds1 ds2 c st1' st2' m1' m2' b1 b2 os1 os2 ds1' ds2',
  ds2 ++ ds2' = ds1 ++ ds1' ->
  P ;; PA |-ct- c ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA m1 m2) ->
  P |-i <(st1, m1, b, ds1)> =[ c ]=> <(st1', m1', b1, os1)>  ->
  P |-i <(st2, m2, b, ds2)> =[ c ]=> <(st2', m2', b2, os2)> ->
  ds1 = ds2 /\ ds1' = ds2'.
Proof.
  intros P PA st1 st2 m1 m2 b ds1 ds2 c st1' st2' m1' m2' b1 b2 os1 os2 ds1' ds2'
    Hds Hwt Heq Haeq Heval1 Heval2.
  pose proof Hds as H.
  symmetry in H.
  apply app_eq_prefix in H.
  eapply ct_well_typed_ideal_noninterferent_general in H;
    [ | | | | apply Heval1 | apply Heval2]; try eassumption.
  - destruct H as [ _ [ _ [ _ H] ] ]. subst. split; [reflexivity|].
    apply app_inv_head in Hds. congruence.
Qed.

Theorem ideal_spec_ct_secure :
  forall P PA c st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    (b = false -> pub_equiv PA m1 m2) ->
    P |-i <(st1, m1, b, ds)> =[ c ]=> <(st1', m1', b1', os1)> ->
    P |-i <(st2, m2, b, ds)> =[ c ]=> <(st2', m2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c st1 st2 m1 m2 b st1' st2' m1' m2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2. generalize dependent b2'.
  induction Heval1; intros b2' os2' m2 Haeq m2' st2 Heq st2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) reflexivity.
  - (* Skip *) reflexivity.
  - (* Seq *)
    eapply aux in H1; [| | | | apply Heval1_1 | apply H5 ]; eauto.
    destruct H1 as [H1 H1']. subst.
    assert(NI1 : pub_equiv P st' st'0 /\ b' = b'0 /\ (b' = false -> pub_equiv PA m' m'0)).
    { eapply ct_well_typed_ideal_noninterferent; [ | | | eassumption | eassumption]; eauto. }
    destruct NI1 as [NI1eq [NIb NIaeq] ]. subst.
    erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
  - (* If *)
    f_equal.
    + f_equal. eapply noninterferent_exp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (eval st be); eassumption).
      subst c c4. erewrite (noninterferent_exp Heq H14); eassumption.
  - (* If_F *)
    f_equal.
    + f_equal. eapply noninterferent_exp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (eval st be); eassumption).
      * intro contra. discriminate contra.
      * subst c c4. erewrite noninterferent_exp; eassumption.
  - (* While *) eapply IHHeval1; eauto.
  - (* ALoad *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* ALoad_U *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* AStore *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* AStore *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
Qed.

(* ================================================================= *)
(** ** Correctness of sel_slh as a compiler from ideal to speculative semantics *)

(** We now prove that the ideal semantics correctly captures the programs
    produced by [sel_slh] when executed using the speculative semantics. We
    phrase this as a backwards compiler correctness proof for [sel_slh],
    which intuitively looks as follows:

    <(st,m,b,ds)> =[[ sel_slh P c ]]=> <(st',m',b',os)> ->
    P |-i <(st,m,b,ds)> =[[ c ]]=> <(msf!->st msf;st',m',b',os)>
*)

(** All results about [sel_slh] below assume that the original [c] doesn't
    already use the variable [msf] needed by the [sel_slh] translation. *)

Fixpoint e_unused (x:string) (e:exp) : Prop :=
  match e with
  | ANum n      => True
  | AId y       => y <> x
  | ABin _ e1 e2 => e_unused x e1 /\ e_unused x e2
  | <{b ? e1 : e2}> => e_unused x b /\ e_unused x e1 /\ e_unused x e2
  end.

Fixpoint unused (x:string) (c:com) : Prop :=
  match c with
  | <{{skip}}> => True
  | <{{y := e}}> => y <> x /\ e_unused x e
  | <{{c1; c2}}> => unused x c1 /\ unused x c2
  | <{{if be then c1 else c2 end}}> =>
      e_unused x be /\ unused x c1 /\ unused x c2
  | <{{while be do c end}}> => e_unused x be /\ unused x c
  | <{{y <- a[[i]]}}> => y <> x /\ e_unused x i
  | <{{a[i] <- e}}> => e_unused x i /\ e_unused x e
  end.

(** As a warm-up we prove that [sel_slh] properly updates the variable msf. *)

(** Proving this by induction on [com] or [spec_eval] leads to induction
    hypotheses, that are not strong enough to prove the [Spec_While]
    case. Therefore we will prove it by induction on the [size]
    of a the pair of the [(c:com)] and the [(ds:dirs)]. *)

Fixpoint com_size (c:com) : nat :=
  match c with
  | <{{ c1; c2 }}> => 1 + (com_size c1) + (com_size c2)
  | <{{ if be then ct else cf end }}> => 1 + max (com_size ct) (com_size cf)
  | <{{ while be do cw end }}> => 1 + (com_size cw)
  | <{{ skip }}> => 1
  | _  => 1
  end.

Definition size (c:com) (ds:dirs) : nat := com_size c + length ds.

(** We prove a helpful induction principle on [size]: *)

Check measure_induction.

Lemma size_ind : forall P : com -> dirs -> Prop,
  (forall c ds,
    (forall c' ds', size c' ds' < size c ds -> P c' ds') ->
    P c ds) ->
  (forall c ds, P c ds).
Proof.
  intros.
  remember (fun c_ds => P (fst c_ds) (snd c_ds)) as P'.
  replace (P c ds) with (P' (c, ds)) by now rewrite HeqP'.
  eapply measure_induction with (f:=fun c_ds => size (fst c_ds) (snd c_ds)).
  intros. rewrite HeqP'.
  apply H. intros.
  remember (c', ds') as c_ds'.
  replace (P c' ds') with (P' c_ds') by now rewrite Heqc_ds', HeqP'.
  apply H0. now rewrite Heqc_ds'.
Qed.

(** The proof of [sel_slh_flag] *)

Lemma size_decreasing: forall c1 ds1 c2 ds2,
  (com_size c1 < com_size c2 /\ length ds1 <= length ds2 ) \/
  (com_size c1 <= com_size c2 /\ length ds1 < length ds2) ->
  size c1 ds1 < size c2 ds2.
Proof.
  intros c1 ds1 c2 ds2 [ [Hcom Hdir] | [Hcom Hdir] ];
  unfold size; lia.
Qed.

(** Based on the Lemma [size_decreasing] we can build a tactic to solve
    the subgoals in the form of [size c' ds' < size c ds],
    which will be produced by [size_ind].*)

Ltac size_auto :=
  try ( apply size_decreasing; left; split; simpl;
        [| repeat rewrite length_app]; lia );
  try ( apply size_decreasing; right; split; simpl;
        [| repeat rewrite length_app]; lia);
  try ( apply size_decreasing; left; split; simpl;
        [auto | repeat rewrite length_app; lia] ).

(** To properly apply [size_ind], we need to state [sel_slh_flag]
    as a proposition of type [com -> dirs -> Prop]. Therefore we define the
    following: *)

Definition sel_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall P st m (b:bool) st' m' (b':bool) os,
  unused msf c ->
  st msf = (if b then 1 else 0) ->
  <(st, m, b, ds)> =[ sel_slh P c ]=> <(st', m', b', os)> ->
  st' msf = (if b' then 1 else 0).

Lemma sel_slh_flag : forall c ds,
  sel_slh_flag_prop c ds.
Proof.
  eapply size_ind. unfold sel_slh_flag_prop.
  intros c ds IH P st m b st' m' b' os Hunused Hstb Heval.
  destruct c; simpl in *; try (now inversion Heval; subst; eauto).
  - (* Asgn *)
    inversion Heval; subst. rewrite t_update_neq; tauto.
  - (* Seq *)
    inversion Heval; subst; clear Heval.
    apply IH in H1; try tauto.
    + apply IH in H10; try tauto. size_auto.
    + size_auto.
  - (* IF *)
    inversion Heval; subst; clear Heval.
    + (* Spec_If *)
      destruct (eval st be) eqn:Eqnbe.
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
      * (* analog to true case *)
        inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11.
        { auto. }
        { size_auto. }
        { tauto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
    + (* Spec_If_F; analog to Spec_If case *)
      destruct (eval st be) eqn:Eqnbe.
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. simpl. reflexivity. }
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. simpl. reflexivity. }
  - (* While *)
      inversion Heval; subst; clear Heval.
      inversion H1; subst; clear H1.
      inversion H11; subst; clear H11.
      + (* non-speculative *)
        destruct (eval st be) eqn:Eqnbe.
        * inversion H12; subst; clear H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. assumption.
        * inversion H12; subst; clear H12.
          assert(Hwhile: <(st'1, m'1, b'1, (ds0 ++ ds2)%list)>
              =[ sel_slh P <{{while be do c end}}> ]=> <(st', m', b', (os3++os2)%list)> ).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { size_auto. }
          { clear Hwhile; clear H11.
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2. simpl in H12.
            apply IH in H12; try tauto.
            - size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. assumption. }
      + (* speculative; analog to non_speculative case *)
        destruct (eval st be) eqn:Eqnbe.
        * inversion H12; subst; clear H12.
          assert(Hwhile: <(st'1, m'1, b'1, (ds0 ++ ds2)%list)>
              =[sel_slh P <{{while be do c end}}>]=> <(st', m', b', (os3++os2)%list )>).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { size_auto. }
          { clear Hwhile; clear H11.
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2. simpl in H12.
            apply IH in H12; try tauto.
            - size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. reflexivity. }
        * inversion H12; subst; clear H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. reflexivity.
  - (* ALoad *)
    destruct (P x) eqn:Eqnbe.
    + inversion Heval; subst; clear Heval.
      inversion H10; subst; clear H10.
      rewrite t_update_neq; [| tauto].
      inversion H1; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
    + inversion Heval; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
Qed.

(** We need a few more lemmas before we prove backwards compiler correctness *)

Lemma eval_unused_update : forall X st n,
  (forall ae, e_unused X ae ->
    eval (X !-> n; st) ae = eval st ae).
Proof.
  intros X st n. induction ae; intros; simpl in *; try reflexivity.
  - rewrite t_update_neq; eauto.
  - destruct H.
    rewrite IHae1; [| tauto]. rewrite IHae2; [| tauto].
    reflexivity.
  - destruct H. destruct H0.
    rewrite IHae1, IHae2, IHae3; auto.
Qed.

Lemma ideal_unused_overwrite: forall P st m b ds c st' m' b' os X n,
  unused X c ->
  P |-i <(st, m, b, ds)> =[ c ]=> <(st', m', b', os)> ->
  P |-i <(X !-> n; st, m, b, ds)> =[ c ]=> <(X !-> n; st', m', b', os)>.
Proof.
  intros P st m b ds c st' m' b' os X n Hu H.
  induction H; simpl in Hu.
  - (* Skip *) econstructor.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    econstructor. rewrite eval_unused_update; tauto.
  - (* Seq *)
    econstructor.
    + apply IHideal_eval1; tauto.
    + apply IHideal_eval2; tauto.
  - (* If *)
    rewrite <- eval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite eval_unused_update; [ | tauto].
    destruct (eval st be) eqn:D; apply IHideal_eval; tauto.
  - (* If_F *)
    rewrite <- eval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite eval_unused_update; [ | tauto].
    destruct (eval st be) eqn:D; apply IHideal_eval; tauto.
  - (* While *)
    econstructor. apply IHideal_eval. simpl; tauto.
  - (* ALoad *)
    rewrite t_update_permute; [| tauto]. econstructor; [ | assumption].
    rewrite eval_unused_update; tauto.
  - (* ALoad_U *)
    rewrite t_update_permute; [| tauto]. econstructor; try assumption.
    rewrite eval_unused_update; tauto.
  - (* AStore *)
    econstructor; try assumption.
    + rewrite eval_unused_update; tauto.
    + rewrite eval_unused_update; tauto.
  - (* AStore_U *)
    econstructor; try assumption.
    + rewrite eval_unused_update; tauto.
    + rewrite eval_unused_update; tauto.
Qed.

Lemma ideal_unused_update : forall P st m b ds c st' m' b' os X n,
  unused X c ->
  P |-i <(X !-> n; st, m, b, ds)> =[ c ]=> <(X !-> n; st', m', b', os)> ->
  P |-i <(st, m, b, ds)> =[ c ]=> <(X !-> st X; st', m', b', os)>.
Proof.
  intros P st m b ds c st' m' b' os X n Hu Heval.
  eapply ideal_unused_overwrite with (X:=X) (n:=(st X)) in Heval; [| assumption].
  do 2 rewrite t_update_shadow in Heval. rewrite t_update_same in Heval. assumption.
Qed.

Lemma ideal_unused_update_rev : forall P st m b ds c st' m' b' os X n,
  unused X c ->
  P |-i <(st, m, b, ds)> =[ c ]=> <(X!-> st X; st', m', b', os)> ->
  P |-i <(X !-> n; st, m, b, ds)> =[ c ]=> <(X !-> n; st', m', b', os)>.
Proof.
  intros P st m b ds c st' m' b' os X n Hu H.
  eapply ideal_unused_overwrite in H; [| eassumption].
  rewrite t_update_shadow in H. eassumption.
Qed.

(** The backwards compiler correctness proof uses [size_ind]: *)

Definition sel_slh_compiler_correctness_prop (c:com) (ds:dirs) : Prop :=
  forall P st m (b: bool) st' m' b' os,
  unused msf c ->
  st msf = (if b then 1 else 0) ->
  <(st, m, b, ds)> =[ sel_slh P c ]=> <(st', m', b', os)> ->
  P |-i <(st, m, b, ds)> =[ c ]=> <(msf !-> st msf; st', m', b', os)>.

Lemma sel_slh_compiler_correctness : forall c ds,
  sel_slh_compiler_correctness_prop c ds.
Proof.
  apply size_ind. unfold sel_slh_compiler_correctness_prop.
  intros c ds IH P st m b st' m' b' os Hunused Hstb Heval.
  destruct c; simpl in *; inversion Heval; subst; clear Heval;
  try (destruct (P x); discriminate).
  - (* Skip *)
    rewrite t_update_same. apply Ideal_Skip.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    rewrite t_update_same.
    constructor. reflexivity.
  - (* Seq *)
    eapply Ideal_Seq.
    + apply IH in H1; try tauto.
      * eassumption.
      * size_auto.
    + apply sel_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * size_auto.
  (* IF *)
  - (* non-speculative *)
    destruct (eval st be) eqn:Eqnbe; inversion H10;
    inversion H1; subst; clear H10; clear H1; simpl in *.
    + apply IH in H11; try tauto.
      * rewrite <- Eqnbe. apply Ideal_If. rewrite Eqnbe in *.
        rewrite t_update_same in H11. apply H11.
      * size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
    + (* analog to false case *)
      apply IH in H11; try tauto.
      * rewrite <- Eqnbe. apply Ideal_If. rewrite Eqnbe in *.
        rewrite t_update_same in H11. apply H11.
      * size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
  - (* speculative *)
    destruct (eval st be) eqn:Eqnbe; inversion H10; inversion H1;
    subst; simpl in *; clear H10; clear H1; rewrite Eqnbe in H11.
    + rewrite <- Eqnbe. apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * size_auto.
    + (* analog to false case *)
      rewrite <- Eqnbe. apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * size_auto.
  - (* While *)
    eapply Ideal_While.
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11; simpl in *.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl.
      apply Ideal_If.
      destruct (eval st be) eqn:Eqnbe.
      * inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqnbe. do 2 rewrite t_update_same.
        apply Ideal_Skip.
      * inversion H12; subst; clear H12.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2; simpl in *.
        assert(Hwhile: <(st'1, m'1, b'1, ds2)>
          =[ sel_slh P <{{while be do c end}}> ]=> <(st', m', b', os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        do 2 rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13. rewrite t_update_same in H13.
          apply IH in H13; try tauto.
          - eassumption.
          - size_auto. }
        { apply IH in Hwhile; auto.
          - eapply ideal_unused_update_rev; eauto.
          - size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite t_update_eq. rewrite Eqnbe. assumption. }
    + (* speculative; analog to non_speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl.
      apply Ideal_If_F.
      destruct (eval st be) eqn:Eqnbe.
      * inversion H12; subst; clear H12.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2; simpl in *.
        assert(Hwhile: <(st'1, m'1, b'1, ds2)>
          =[ sel_slh P <{{while be do c end}}> ]=> <(st', m', b', os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        do 2 rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13.
          apply IH in H13; try tauto.
          - rewrite t_update_eq in H13.
            apply ideal_unused_update in H13; [| tauto].
            eassumption.
          - size_auto. }
        { apply IH in Hwhile; auto.
          - rewrite Eqnbe in H13.
            apply IH in H13; try tauto.
            + apply ideal_unused_update_rev; eauto.
            + size_auto.
          - size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite Eqnbe. rewrite t_update_eq. reflexivity. }
      * inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqnbe. rewrite t_update_shadow. rewrite t_update_same.
        apply Ideal_Skip.
  (* ALoad *)
  - (* Spec_ALoad; public *)
    destruct (P x) eqn:Heq; try discriminate H.
    injection H; intros; subst; clear H.
    inversion H1; clear H1; subst. rewrite <- app_nil_r in *.
    inversion H0; clear H0; subst; simpl in *.
    * (* Ideal_ALoad *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      rewrite t_update_eq. simpl.
      rewrite <- Hstb at 1. rewrite t_update_same.
      replace (not_zero (bool_to_nat (negb (not_zero
        (bool_to_nat ((if b' then 1 else 0) =? 0)%nat)) || not_zero 0))) with (b' && (P x))
          by (rewrite Heq; destruct b'; simpl; reflexivity).
        eapply Ideal_ALoad; eauto.
    * (* Ideal_ALoad_U *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      simpl. rewrite <- Hstb at 1. rewrite t_update_same.
      replace (x !-> 0; st) with (x !-> if P x then 0 else nth i' (m' a') 0; st)
        by (rewrite Heq; reflexivity).
      eapply Ideal_ALoad_U; eauto.
  - (* Spec_ALoad; secret*)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> nth (eval st i) (m' a) 0; st)
      with (x !-> if b' && P x then 0 else nth (eval st i) (m' a) 0; st)
        by (rewrite Heq; destruct b'; reflexivity).
    eapply Ideal_ALoad; eauto.
  - (* Spec_ALoad_U *)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> nth i' (m' a') 0; st)
      with (x !-> if P x then 0 else nth i' (m' a') 0; st)
        by (rewrite Heq; reflexivity).
    eapply Ideal_ALoad_U; eauto.
  (* AStore *)
  - (* Spec_AStore *)
    rewrite t_update_same. apply Ideal_AStore; tauto.
  - (* Spec_AStore_U *)
    rewrite t_update_same. apply Ideal_AStore_U; tauto.
Qed.

(* ================================================================= *)
(** ** Speculative constant-time security for Selective SLH *)

(** Finally, we use compiler correctness and [spec_ct_secure] for the ideal
    semantics to prove [spec_ct_secure] for [sel_slh]. *)

Theorem sel_slh_spec_ct_secure :
  forall P PA c st1 st2 m1 m2 st1' st2' m1' m2' b1' b2' os1 os2 ds,
  P ;; PA |-ct- c ->
  unused msf c ->
  st1 msf = 0 ->
  st2 msf = 0 ->
  pub_equiv P st1 st2 ->
  pub_equiv PA m1 m2 ->
  <(st1, m1, false, ds)> =[ sel_slh P c ]=> <(st1', m1', b1', os1)> ->
  <(st2, m2, false, ds)> =[ sel_slh P c ]=> <(st2', m2', b2', os2)> ->
  os1 = os2.
Proof.
  intros P PA c st1 st2 m1 m2 st1' st2' m1' m2' b1' b2' os1 os2 ds
    Hwt Hunused Hs1b Hs2b Hequiv Haequiv Heval1 Heval2.
  eapply sel_slh_compiler_correctness in Heval1; try assumption.
  eapply sel_slh_compiler_correctness in Heval2; try assumption.
  eapply ideal_spec_ct_secure; eauto.
Qed.

(* ################################################################# *)
(** * Monadic interpreter for speculative semantics (optional; text missing) *)

Module SpecCTInterpreter.

(** Since manually constructing directions for the proofs of examples is very
    time consuming, we introduce a sound monadic interpreter, which can be used
    to simplify the proofs of the examples. *)

(** The Rocq development below is complete, but the text about it is missing.
    Readers not familiar with monadic interpreters can safely skip this section. *)

Definition prog_st : Type :=  state * mem * bool * dirs * obs.

Inductive output_st (A : Type): Type :=
| OST_Error : output_st A
| OST_OutOfFuel : output_st A
| OST_Finished : A -> prog_st -> output_st A.

Definition evaluator (A : Type): Type := prog_st -> (output_st A).
Definition interpreter : Type := evaluator unit.

Definition ret {A : Type} (value : A) : evaluator A :=
  fun (pst: prog_st) => OST_Finished A value pst.

Definition bind {A : Type} {B : Type} (e : evaluator A) (f : A -> evaluator B): evaluator B :=
  fun (pst: prog_st) =>
    match e pst with
    | OST_Finished _ value (st', m', b', ds', os1)  =>
        match (f value) (st', m', b', ds', os1) with
        | OST_Finished _ value (st'', m'', b'', ds'', os2) =>
            OST_Finished B value (st'', m'', b'', ds'', os2)
        | ret => ret
        end
    | OST_Error _ => OST_Error B
    | OST_OutOfFuel _ => OST_OutOfFuel B
    end.

Notation "e >>= f" := (bind e f) (at level 58, left associativity).
Notation "e >> f" := (bind e (fun _ => f)) (at level 58, left associativity).

(* ================================================================= *)
(** ** Helper functions for individual instructions *)

Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  fun (pst : prog_st) =>
    let
      '(st, _, _, _, _) := pst
    in
      ret (st name) pst.

Definition set_var (name : string) (value : nat) : interpreter :=
  fun (pst: prog_st) =>
    let
      '(st, m, b, ds, os) := pst
    in
      let
        new_st := (name !-> value; st)
      in
        finish (new_st, m, b, ds, os).

Definition get_arr (name : string): evaluator (list nat) :=
  fun (pst: prog_st) =>
    let
      '(_, m, _, _, _) := pst
    in
      ret (m name) pst.

Definition set_arr (name : string) (value : list nat) : interpreter :=
  fun (pst : prog_st) =>
    let '(st, m, b, ds, os) := pst in
    let new_m := (name !-> value ; m) in
    finish (st, new_m, b, ds, os).

Definition start_speculating : interpreter :=
  fun (pst : prog_st) =>
    let '(st, m, _, ds, os) := pst in
    finish (st, m, true, ds, os).

Definition is_speculating : evaluator bool :=
  fun (pst : prog_st) =>
    let '(_, _, b, _, _) := pst in
    ret b pst.

Definition eval_exp (a : exp) : evaluator nat :=
  fun (pst: prog_st) =>
    let '(st, _, _, _, _) := pst in
    let v := eval st a in
    ret v pst.

Definition raise_error : interpreter :=
  fun _ => OST_Error unit.

Definition observe (o : observation) : interpreter :=
  fun (pst : prog_st) =>
    let '(st, m, b, ds, os) := pst in
    OST_Finished unit tt (st, m, b, ds, (os ++ [o])%list).

Definition fetch_direction : evaluator (option direction) :=
  fun (pst : prog_st) =>
    let '(st, m, b, ds, os) := pst in
    match ds with
    | d::ds' =>
        ret (Some d) (st, m, b, ds', os)
    | [] => ret None (st, m, b, [], os)
    end.

(* ================================================================= *)
(** ** The actual speculative interpreter *)

Fixpoint spec_eval_engine_aux (fuel : nat) (c : com) : interpreter :=
  match fuel with
  | O => fun _ => OST_OutOfFuel unit
  | S fuel =>
    match c with
    | <{ skip }> => finish
    | <{ x := e }> => eval_exp e >>= fun v => set_var x v
    | <{ c1 ; c2 }> =>
        spec_eval_engine_aux fuel c1 >>
        spec_eval_engine_aux fuel c2
    | <{ if be then ct else cf end }> =>
        eval_exp be >>= fun bool_value =>
          observe (OBranch (not_zero bool_value)) >> fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if not_zero bool_value then spec_eval_engine_aux fuel ct
              else spec_eval_engine_aux fuel cf
          | Some DForce =>
              start_speculating >>
              if not_zero bool_value then spec_eval_engine_aux fuel cf
              else spec_eval_engine_aux fuel ct
          | _ => raise_error
          end
    | <{ while be do c end }> =>
        spec_eval_engine_aux fuel <{if be then c; while be do c end else skip end}>
    | <{ x <- a[[ie]] }> =>
        eval_exp ie >>= fun i => observe (OALoad a i) >> get_arr a >>=
        fun arr_a => is_speculating >>= fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_var x (nth i arr_a 0)
              else raise_error
          | Some (DLoad a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat && (i' <? List.length arr_a')%nat && b then
                  set_var x (nth i' arr_a' 0)
                else raise_error
          | _ => raise_error
          end
    | <{ a[ie] <- e }> =>
        eval_exp ie >>= fun i => observe (OAStore a i) >> get_arr a >>=
        fun arr_a => eval_exp e >>= fun n => is_speculating >>= fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_arr a (upd i arr_a n)
              else raise_error
          | Some (DStore a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat && (i' <? List.length arr_a')%nat && b then
                  set_arr a' (upd i' arr_a' n)
                else raise_error
          | _ => raise_error
          end
    end
end.

Definition compute_fuel (c :com) (ds :dirs) : nat :=
  2 +
    match ds with
    | [] => com_size c
    | _ => length ds * com_size c
    end.

Definition spec_eval_engine (c : com) (st : state) (m : mem) (b : bool) (ds : dirs)
      : option (state * mem * bool * obs) :=
    match spec_eval_engine_aux (compute_fuel c ds) c (st, m, b, ds, []) with
    | OST_Finished _ _ (st', m', b', ds', os) =>
        if ((length ds') =? 0)%nat then Some (st', m', b', os)
        else None
    | _ => None
    end.

(* ================================================================= *)
(** ** Soundness of the interpreter *)

Lemma ltb_reflect : forall n m :nat,
  reflect (n < m) (n <? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite ltb_lt. reflexivity.
Qed.

Lemma eqb_reflect: forall n m :nat,
  reflect (n = m ) (n =? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Lemma spec_eval_engine_aux_sound : forall n c st m b ds os st' m' b' ds' os' u,
  spec_eval_engine_aux n c (st, m, b, ds, os)
    = OST_Finished unit u (st', m', b', ds', os') ->
  (exists dsn osn,
  (dsn++ds')%list = ds /\ (os++osn)%list = os' /\
      <(st, m, b, dsn)> =[ c ]=> <(st', m', b', osn)> ).
Proof.
  induction n as [| n' IH]; intros c st m b ds os st' m' b' ds' os' u Haux;
  simpl in Haux; [discriminate |].
  destruct c as [| X e | c1 c2 | be ct cf | be cw | X a ie | a ie e ] eqn:Eqnc;
  unfold ">>=" in Haux; simpl in Haux.
  - (* Skip *)
    inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Skip.
  - (* Asgn *)
    simpl in Haux. inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Asgn. reflexivity.
  - destruct (spec_eval_engine_aux _ c1 _) eqn:Hc1;
    try discriminate; simpl in Haux.
    destruct p as [ [ [ [stm mm] bm] dsm] osm]; simpl in Haux.
    destruct (spec_eval_engine_aux _ c2 _) eqn:Hc2;
    try discriminate; simpl in Haux.
    destruct p as [ [ [ [stt mt] bt] dst] ost]; simpl in Haux.
    apply IH in Hc1. destruct Hc1 as [ds1 [ os1 [Hds1 [Hos1 Heval1] ] ] ].
    apply IH in Hc2. destruct Hc2 as [ds2 [ os2 [Hds2 [Hos2 Heval2] ] ] ].
    inversion Haux; subst. exists (ds1++ds2)%list; exists (os1++os2)%list;
    split; [| split].
    + rewrite <- app_assoc. reflexivity.
    + rewrite <- app_assoc. reflexivity.
    + eapply Spec_Seq; eauto.
  - (* IF *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (eval st be) eqn:Eqnbe.
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' cf (st, m, b, ds_tl, (os ++ [OBranch false])%list)) eqn:Hcf;
        try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt mt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DStep :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_O; [| eassumption].
          apply Spec_If. rewrite Eqnbe. apply Heval. }
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' ct (st, m, b, ds_tl, (os ++ [OBranch true])%list)) eqn:Hct;
        try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt mt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DStep :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_S; [| eassumption].
          apply Spec_If. rewrite Eqnbe. apply Heval. }
    + (* DForce *)
      destruct (eval st be) eqn:Eqnbe.
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' ct (st, m, true, ds_tl, (os ++ [OBranch false])%list)) eqn:Hcf;
        try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt mt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DForce :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_O; [| eassumption].
          apply Spec_If_F. rewrite Eqnbe. apply Heval. }
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' cf (st, m, true, ds_tl, (os ++ [OBranch true])%list)) eqn:Hct; try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt mt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DForce :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_S; [| eassumption].
          apply Spec_If_F. rewrite Eqnbe. apply Heval. }
  - (* While *)
    apply IH in Haux. destruct Haux as [dst [ ost [Hds [Hos Heval] ] ] ].
    exists dst; exists ost; split; [| split]; eauto.
  - (* ALoad *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (eval st ie <? Datatypes.length (m a))%nat eqn:Eqnindex; try discriminate.
      destruct (observe (OALoad a (eval st ie)) (st, m, b, ds_tl, os)) eqn:Eqbobs; try discriminate;
      simpl in Haux. inversion Haux; subst.
      eexists [DStep]; eexists [OALoad a (eval st ie)]; split;[| split]; try reflexivity.
      eapply Spec_ALoad; eauto. destruct (ltb_reflect (eval st ie) (length (m' a))) as [Hlt | Hgeq].
      * apply Hlt.
      * discriminate.
    + (* DForce *)
      destruct (negb (eval st ie <? Datatypes.length (m a))%nat) eqn:Eqnindex1;
      destruct ((i <? Datatypes.length (m a0))%nat) eqn:Eqnindex2;
      destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
      eexists [DLoad a0 i ]; eexists [OALoad a (eval st ie)]; split;[| split]; try reflexivity.
      eapply Spec_ALoad_U; eauto.
      * destruct (ltb_reflect (eval st ie) (length (m' a))) as [Hlt | Hgeq].
        { discriminate. }
        { apply not_lt in Hgeq. apply Hgeq. }
      * destruct (ltb_reflect i (length (m' a0))) as [Hlt | Hgeq].
        { apply Hlt. }
        { discriminate. }
  - (* AStore *)
  destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
  destruct d eqn:Eqnd; try discriminate; simpl in Haux.
  + (* DStep *)
    destruct ((eval st ie <? Datatypes.length (m a))%nat) eqn:Eqnindex; try discriminate.
    destruct (observe (OAStore a (eval st ie)) (st, m, b, ds_tl, os)) eqn:Eqbobs; try discriminate;
    simpl in Haux. inversion Haux; subst.
    eexists [DStep]; eexists [OAStore a (eval st' ie)]; split;[| split]; try reflexivity.
    eapply Spec_AStore; eauto. destruct (ltb_reflect (eval st' ie) (length (m a))) as [Hlt | Hgeq].
    * apply Hlt.
    * discriminate.
  + (* DForce *)
    destruct  (negb (eval st ie <? Datatypes.length (m a))%nat) eqn:Eqnindex1;
    destruct (i <? Datatypes.length (m a0))%nat eqn:Eqnindex2;
    destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
    eexists [DStore a0 i]; eexists [OAStore a (eval st' ie)]; split;[| split]; try reflexivity.
    eapply Spec_AStore_U; eauto.
    * destruct (ltb_reflect (eval st' ie) (length (m a))) as [Hlt | Hgeq].
      { discriminate. }
      {  apply not_lt in Hgeq. apply Hgeq. }
    * destruct (ltb_reflect i (length (m a0))) as [Hlt | Hgeq].
      { apply Hlt. }
      { discriminate. }
Qed.

Theorem spec_eval_engine_sound: forall c st m b ds st' m' b' os',
  spec_eval_engine c st m b ds = Some (st', m', b', os') ->
  <(st, m, b, ds)> =[ c ]=> <(st', m', b', os')> .
Proof.
  intros c st m b ds st' m' b' os' Hengine.
  unfold spec_eval_engine in Hengine.
  destruct (spec_eval_engine_aux _ c _) eqn:Eqnaux;
  try discriminate. destruct p as [ [ [ [stt mt] bt] dst] ost].
  destruct ((Datatypes.length dst =? 0)%nat) eqn:Eqnds; try discriminate.
  apply spec_eval_engine_aux_sound in Eqnaux.
  destruct Eqnaux as [dsn [osn [Hdsn [Hosn Heval] ] ] ].
  inversion Hengine; subst. rewrite app_nil_l.
  destruct (eqb_reflect (length dst) 0) as [Heq | Hneq].
  + apply length_zero_iff_nil in Heq. rewrite Heq. rewrite app_nil_r. apply Heval.
  + discriminate.
Qed.

(* ================================================================= *)
(** ** Back to showing that our example is not speculative constant-time *)

Example spec_insecure_prog_2_is_spec_insecure :
  ~(spec_ct_secure XYZpub APpub spec_insecure_prog_2).
Proof.
  unfold spec_insecure_prog_2.
  (* program is insecure under speculative execution. *)
  remember (__ !-> 0) as st.
  remember (AP!-> [0;1;2]; AS !-> [0;0;0;0]; __ !-> []) as m1.
  remember (AP!-> [0;1;2]; AS !-> [4;5;6;7]; __ !-> []) as m2.
  remember ([DStep; DStep; DStep; DStep; DStep; DStep; DForce; DLoad AS 3; DStep; DStep]) as ds.
  intros Hsecure.
  assert (L: exists stt1 mt1 bt1 os1 stt2 mt2 bt2 os2,
    <(st, m1, false, ds )> =[ spec_insecure_prog_2 ]=> <( stt1, mt1, bt1, os1)> /\
    <(st, m2, false, ds )> =[ spec_insecure_prog_2 ]=> <( stt2, mt2, bt2, os2)> /\
    os1 <> os2 ).
  { eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
    split; [| split].
    - apply spec_eval_engine_sound. unfold spec_insecure_prog_2, spec_eval_engine;
      subst; simpl; reflexivity.
    - apply spec_eval_engine_sound. unfold spec_insecure_prog_2, spec_eval_engine;
      subst; simpl; reflexivity.
    - intros Contra; inversion Contra. }
  destruct L as [stt1 [mt1 [bt1 [os1 [stt2 [mt2 [bt2 [os2 [Heval1 [Heval2 Hneq] ] ] ] ] ] ] ] ] ].
  eapply Hsecure in Heval1; eauto.
  - apply pub_equiv_refl.
  - subst. apply pub_equiv_update_public; auto.
    apply pub_equiv_update_secret; auto.
    apply pub_equiv_refl.
Qed.

End SpecCTInterpreter.

(* 2026-01-07 13:37 *)
