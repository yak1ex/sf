(** * Noninterference: Defining Secrecy and Secure Multi-Execution *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
From SECF Require Import Maps.
From SECF Require Import Imp.
Set Default Goal Selector "!".

From Stdlib Require Import Lia.

(** Programmers have to be very careful about how information flows in
    the software they develop to prevent leaking secret data. For
    instance, in course management systems students shouldn't be able
    to obtain information about other student's grades. In crypto
    protocols the keys should be kept secret and not sent over the
    network in the clear. *)

(** Information-flow control tries to prevent leaking secret
    information.  But how does one formalize that a program doesn't
    leak any information about the secret inputs to public outputs? *)

(** We first investigate this question in the very simple setting of Rocq
    functions taking two arguments, one we call the public input and the other
    one we call the secret input. Our functions return a pair where the first
    element is the public output and the second one the secret output. *)

(** Say we have the following function working on natural numbers: *)

Definition secure_f (pi si : nat) : nat*nat := (pi+1, pi+si*2).

(** This function seems intuitively secure, since the first output [pi+1], which
    we assume to be public, only depends on the public input [pi], but not on
    the secret input [si]. The second output [pi+si*2] depends on both the
    public input and the secret input, but that's okay, since we assume this
    second output to be secret. *)

(** Still, how can we mathematically define that this function is
    secure? Let's try it on a couple of inputs: *)

Example example1_secure_f : secure_f 0 0 = (1,0).
Proof. reflexivity. Qed.

Example example2_secure_f : secure_f 0 1 = (1,2).
Proof. reflexivity. Qed.

Example example3_secure_f : secure_f 1 2 = (2,5).
Proof. reflexivity. Qed.

(** In the last two cases the value of the public output is equal to the value
    of secret input. But that's just a coincidence, and has nothing to do with
    the public output leaking the secret input, which wasn't used at all in
    computing the public output. *)

(* ################################################################# *)
(** * Naive attempt at defining secrecy *)

(** So a naive security definition, which we'll only use as a strawman, is one
    that simply requires that public outputs are different from secret inputs: *)

Definition broken_sec_def (f : nat -> nat -> nat*nat) :=
  forall pi si, fst (f pi si) <> si.

(** As discussed above, this definition would reject our secure
    function above as insecure: *)

Lemma broken_sec_def_rejects_secure_f : ~broken_sec_def secure_f.
Proof. intros Hc. apply (Hc 0 1). reflexivity. Qed.

(** Even worse, this broken definition of security would allow insecure
    functions, such as the following one whose public output is [si+1]: *)

Definition insecure_f (pi si : nat) : nat*nat := (si+1, pi+si*2).

(** This function's public output is never equal to its secret input, yet an
    attacker can easily compute one from the other by just subtracting [1]. So
    the secret is entirely leaked, yet our broken definition accepts this: *)

Lemma broken_sec_def_accepts_insecure_f : broken_sec_def insecure_f.
Proof.
  unfold broken_sec_def. intros pi si. induction si as [| si' IH].
  - simpl. intros contra. discriminate contra.
  - simpl in *. intro Hc. injection Hc as Hc. apply IH. apply Hc.
Qed.

(** This attempt at defining secure information flow by looking at how
    inputs and outputs are related for a single execution of the
    program was a complete failure. In fact, it is well known in the
    formal security research community that secure information flow
    _cannot_ be defined by looking at just one single program execution. *)

(* ################################################################# *)
(** * Noninterference for pure functions *)

(** The simplest correct way to define secure information flow is a
    property called _noninterference_ [Sabelfeld and Myers 2003] (in Bib.v),
    which in its most standard form looks at _two_ program executions:
    for two different secret inputs the public outputs should not change: *)

Definition noninterferent {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), fst (f pi si1) = fst (f pi si2).

(** This definition prevents secret inputs from interfering with public
    outputs in any way. At the same time it allows secret inputs to
    influence secret outputs and also public inputs to influence both
    public and secret outputs:

                                ┌───╮
                                │ f │
                           pi ─>┼───┼─> po
                                │╲  │
                                │ ╲ │
                                │  ╲│
                           si ─>┼───┼─> so
                                └───╯
*)

(** The definition above defines noninterference for arbitrary types
    of inputs and outputs, so we can instantiate them to [nat] when
    looking at our example functions above: *)

Lemma noninterferent_secure_f : noninterferent secure_f.
Proof. unfold noninterferent, secure_f. simpl. reflexivity. Qed.

Lemma interferent_insecure_f : ~noninterferent insecure_f.
Proof.
  unfold noninterferent. simpl. intros contra.
  specialize (contra 42 0 1). simpl in contra. discriminate contra.
Qed.

(** The [secure_f] function above is quite obviously noninterferent,
    because the expression [pi+1] computing the public output doesn't
    syntactically mention the secret input at all. Since
    noninterference is a semantic property though (not a syntactic
    one), functions where the expression computing the public input
    does syntactically mention the secret input can still be
    noninterferent. Here is a first example: *)

Definition less_obvious_f1 (pi si : nat) : nat*nat := (si * 0, pi+si).

(** This function is noninterferent; since the public output is
    constant [0], so it can't depend on [si], even if it syntactically
    mentions it: *)

Lemma noninterferent_less_obvious_f1 : noninterferent less_obvious_f1.
Proof.
  unfold noninterferent, less_obvious_f1. intros pi si1 si2.
  simpl. repeat rewrite <- mult_n_O. reflexivity.
Qed.



(** Here is another example of a function that is noninterferent, even
    if this is not syntactically obvious: *)

Definition less_obvious_f2 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 1 then si * pi else pi, pi+si).

(** For proving this we show that the public output of this function
    is in fact always equal to just its public input: *)

Lemma aux_f2 : forall si pi, (if Nat.eqb si 1 then si * pi else pi) = pi.
Proof.
  intros si pi. destruct si; simpl.
  - reflexivity.
  - destruct si.
    + simpl. rewrite <- plus_n_O. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma noninterferent_less_obvious_f2 : noninterferent less_obvious_f2.
Proof.
  unfold noninterferent, less_obvious_f2. intros pi si1 si2.
  repeat rewrite aux_f2. simpl. reflexivity.
Qed.

(** Branching on a secret can, however, be dangerous, since one can
    easily leak the secret this way, even if both the [then] and the
    [else] branches are public. For instance the following function
    leaks whether [si] is zero or not, so it is not noninterferent. *)

Definition less_obvious_f3 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 0 then 1 else 0, pi+si).

Lemma interferent_less_obvious_f3 : ~noninterferent less_obvious_f3.
Proof.
  unfold noninterferent, less_obvious_f3. simpl. intros contra.
  specialize (contra 42 0 1). simpl in contra. discriminate contra.
Qed.

(* ================================================================= *)
(** ** Noninterference Exercises *)

(** Let's practice with some "prove or disprove noninterference"
    exercises, for which you are required to give constructive proofs,
    i.e. the use of classical axioms like excluded middle is not allowed. *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f1) *)
Definition obvious_f1 (pi si : nat) : nat*nat := (0,0).

Lemma prove_or_disprove_obvious_f1 :
  noninterferent obvious_f1 \/ ~noninterferent obvious_f1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f2) *)
Definition obvious_f2 (pi si : nat) : nat*nat := (pi+(2*si),(2*pi)+si).

Lemma prove_or_disprove_obvious_f2 :
  noninterferent obvious_f2 \/ ~noninterferent obvious_f2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f4) *)

Definition less_obvious_f4 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 0 then si * pi else pi, pi+si).

(** Is the [less_obvious_f4] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f4 :
  noninterferent less_obvious_f4 \/ ~noninterferent less_obvious_f4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f5) *)

Definition less_obvious_f5 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 0 then si + pi else pi, pi+si).

(** Is the [less_obvious_f5] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f5 :
  noninterferent less_obvious_f5 \/ ~noninterferent less_obvious_f5.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f6) *)

Definition less_obvious_f6 (pi si : nat): nat*nat :=
  (if Nat.ltb si pi then 0 else pi, pi+si).

(** Is the [less_obvious_f6] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f6 :
  noninterferent less_obvious_f6 \/ ~noninterferent less_obvious_f6.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (prove_or_disprove_less_obvious_f7) *)

Definition less_obvious_f7 (pi si : nat): nat*nat :=
  if Nat.eqb (si + pi) 0 then (si,pi) else (pi,si).

Lemma prove_or_disprove_less_obvious_f7 :
  noninterferent less_obvious_f7 \/ ~noninterferent less_obvious_f7.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * A too-strong secrecy definition *)

(** In the definition of noninterference above we pass the same public
    inputs to the two executions and this allows public outputs to
    depend on public inputs. To convince ourselves of this, let's look
    at the following overly strong definition of security: *)

Definition too_strong_sec_def {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi1 pi2:PI) (si1 si2:SI), fst (f pi1 si1) = fst (f pi2 si2).

(** This basically says that the public output of [f] can depend
    neither on the public input not on the secret input, so it has to
    be constant, which is not the case for our [secure_f]. *)

Lemma secure_f_rejected_again : ~too_strong_sec_def secure_f.
Proof.
  unfold too_strong_sec_def, secure_f. simpl. intros contra.
  specialize (contra 0 1 0 0). discriminate contra.
Qed.

(* ################################################################# *)
(** * Noninterferent implies splittable *)

(** Noninterference is still a very strong property, though. In
    particular, [f] being noninterferent is equivalent to [f] being
    splittable into two different functions, one of which doesn't get
    the secret at all. *)

Definition splittable {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  exists (pf : PI -> PO) (sf : PI -> SI -> SO),
    forall pi si , f pi si = (pf pi, sf pi si).

Theorem splittable_noninterferent : forall PI SI PO SO : Type,
  forall f : PI -> SI -> PO*SO, splittable f -> noninterferent f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO f [pf [sf H]] pi si1 si2.
  rewrite H. rewrite H. simpl. reflexivity.
Qed.

Theorem noninterferent_splittable : forall PI SI PO SO : Type,
  forall some_si : SI, (* we require SI to be an inhabited type! *)
  forall f : PI -> SI -> PO*SO, noninterferent f -> splittable f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO some_si f Hni.
  (* we pass the SI inhabitant as a dummy secret value! *)
  exists (fun pi => fst (f pi some_si)).
  exists (fun pi si => snd (f pi si)).
  intros pi si. rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(* ################################################################# *)
(** * Secure Multi-Execution (SME) *)

(** The previous proof also captures the key idea behind Secure
    Multi-Execution (SME) [Devriese and Piessens 2010] (in Bib.v), an
    enforcement mechanism that can make _any_ function
    noninterferent. To achieve this SME runs the function twice, once
    passing a dummy secret as input to obtain the public output, and
    once using the real secret input to obtain the secret output. *)

Definition sme {PI SI PO SO : Type} (some_si : SI)
  (f:PI->SI->PO*SO) : PI->SI->PO*SO :=
    fun pi si => (fst (f pi some_si), snd (f pi si)).

(** Functions protected by [sme] are guaranteed to satisfy noninterference: *)

Theorem noninterferent_sme :  forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent (sme some_si f).
Proof. intros PI SI PO SO some_si f pi si1 si2. simpl. reflexivity. Qed.

(** Moreover, if the function we pass to [sme] is already noninterferent,
    then its behavior will not change; so we say that [sme] is a _transparent_
    enforcement mechanism for noninterference: *)

Theorem transparent_sme : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent f -> forall pi si, f pi si = sme some_si f pi si.
Proof.
  unfold noninterferent, sme. intros PI SI PO SP some_si f Hni pi si.
  rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** It is interesting to look at what [sme] does for _interferent_ functions,
    like [insecure_f], whose public output was one plus its secret input: *)

Example example1_sme_insecure_f: sme 0 insecure_f 0 0 = (1, 0).
Proof. reflexivity. Qed.

Example example2_sme_insecure_f: sme 0 insecure_f 0 1 = (1, 2).
Proof. reflexivity. Qed.

Example example3_sme_insecure_f: sme 0 insecure_f 1 1 = (1, 3).
Proof. reflexivity. Qed.

(** Now the public output of [sme insecure_f 0] is one plus the dummy
   constant [0], so always the constant [1]. *)

Lemma constant_sme_insecure_f: forall pi si,
  fst (sme 0 insecure_f pi si) = 1.
Proof. reflexivity. Qed.

(** This is a secure behavior, but it is different from that of the
    original [insecure_f] function. So we are giving up some
    correctness for security. There is no free lunch! *)

(** Of course the public output of sme does not always become, since
    some functions still use the public input. *)

Definition another_insecure_f (pi si : nat) : nat*nat := (pi+si, pi+si).

Lemma sme_another_insecure_f : forall pi si,
  sme 0 (another_insecure_f) pi si = (pi,pi+si).
Proof. unfold sme, another_insecure_f.
  intros pi si. simpl. rewrite <- plus_n_O. reflexivity. Qed.

(** **** Exercise: 1 star, standard (sme_another_insecure_f2) *)
Definition another_insecure_f2 (pi si : nat) : nat*nat :=
  (if Nat.eqb si 0 then si * pi + pi else pi, pi+si).

Lemma sme_another_insecure_f2 : forall pi si,
    sme 0 (another_insecure_f2) pi si = (pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (sme_another_insecure_f3) *)
Definition another_insecure_f3 (pi si : nat) : nat*nat :=
  (if Nat.eqb si pi then si * pi else pi, pi+si).

Lemma interferent_another_insecure_f3 : ~ noninterferent another_insecure_f3.
Proof.
  unfold noninterferent, another_insecure_f3. simpl.
  intros contra. specialize (contra 8 2 8). simpl in contra. discriminate contra.
Qed.

Lemma sme_another_insecure_f3 : forall pi si,
    sme 0 (another_insecure_f3) pi si = (pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The other downside of [sme] is that we have to run the function
    twice for our two security levels, public and secret. In general,
    we need to run the program as many times as we have security
    levels, which is often an exponential number, say if we take our
    security levels to be sets of principals. This is inefficient!

    Other information-flow control mechanisms overcome this downside,
    but have other downsides of their own, for instance:
        - by requiring nontrivial manual proofs for each individual
          program (e.g., Relational Hoare Logic), or
        - by using static overapproximations that reject some secure
          programs (security type systems), or
        - by using dynamic overapproximations that unnecessarily
          change program behavior, for instance forcefully terminating
          even some secure programs to prevent leaks, in which case
          they are not transparent (dynamic information-flow control;
          an extension of dynamic taint tracking to also handle
          implicit flows).

    Again, there is no free lunch! *)


(* ################################################################# *)
(** * Noninterference for state transformers *)

(** The development above is quite easy to adapt to Rocq functions that
    transform states ([state->state]), where we label each variable as
    either public or secret using a map of type [pub_vars]. *)

Print state. (* state = total_map nat = string -> nat *)

Definition pub_vars := total_map bool. (* = string -> bool *)

(** Instead of requiring that the first elements of two pairs are
    equal, we require that the two states have equal values on the
    variables labeled public by the [pub] map. *)

Definition pub_equiv (pub : pub_vars) (s1 s2 : state) :=
  forall x:string, pub x = true -> s1 x = s2 x.

(** This makes the definition more symmetric, since we can use
    [pub_equiv] both for the input states and the output states: *)

Definition noninterferent_state pub (f : state -> state) :=
  forall s1 s2, pub_equiv pub s1 s2 -> pub_equiv pub (f s1) (f s2).

(** We can prove an equivalence between [noninterferent_state] and our original
    [noninterferent] definition. For this we need to split and merge states.

    We also need a few helper lemmas. *)

(** The way we define [split_state] and [merge_state] is a good example of
    programming with higher-order functions, and there's more of this in
    [Maps].

    The [split_state] function takes a state [s] and zeroes out the variables
    [x] for which [pub x] is different than an argument bit [b]. So
    [split_state s pub true] keeps the public variables, and zeroes out the
    secret ones. Dually, [split_state s pub false] keeps the secret variables,
    and zeroes out the public ones.  *)

Definition split_state (s:state) (pub:pub_vars) (b:bool) : state :=
  fun x : string => if Bool.eqb (pub x) b then s x else 0.

(** The [merge_state] function takes in two states [s1] and [s2]
    and produces a new state that contains the public variables from
    [s1] and the private variables from [s2]. *)

Definition merge_states (s1 s2:state) (pub:pub_vars) : state :=
  fun x : string => if pub x then s1 x else s2 x.

Definition split_state_fun (pub : pub_vars) (mf : state -> state) :=
  fun s1 s2 : state =>
    let ms := mf (merge_states s1 s2 pub) in
    (split_state ms pub true, split_state ms pub false).

(** The technical development needed for the equivalence proof between
    [noninterferent_state] and our original [noninterferent]
    definition is not that interesting though, and one can skip
    directly to the [noninterferent_state_ni] statement on first read. *)

Definition pub_equiv_split (pub : pub_vars) (s1 s2 : state) :=
  forall x:string, (split_state s1 pub true) x = (split_state s2 pub true) x.

Theorem pub_equiv_split_iff : forall pub s1 s2,
  pub_equiv pub s1 s2 <-> pub_equiv_split pub s1 s2.
Proof.
  unfold pub_equiv, pub_equiv_split, split_state. intros. split.
  - intros H x. destruct (Bool.eqb_spec (pub x) true).
    + apply H. apply e.
    + reflexivity.
  - intros H x. specialize (H x). destruct (Bool.eqb_spec (pub x) true).
    + intros _. apply H.
    + contradiction.
Qed.

Theorem pub_equiv_merge_states : forall pub s z1 z2,
  pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub).
Proof.
  unfold pub_equiv, merge_states. intros pub s z1 z2 x Hx.
  rewrite Hx. reflexivity.
Qed.

From Stdlib Require Import FunctionalExtensionality.

Theorem merge_states_split_state : forall s pub,
  merge_states (split_state s pub true) (split_state s pub false) pub = s.
Proof.
  unfold merge_states, split_state. intros s pub.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Heq; reflexivity.
Qed.

(** Now we can finally state our theorem about the equivalence between
    [non_interferent_state] and [noninterferent]: *)

Theorem noninterferent_state_ni : forall pub f,
  noninterferent_state pub f <->
  noninterferent (split_state_fun pub f).
Proof.
  unfold noninterferent_state, noninterferent, split_state_fun.
  intros pub f. split.
  - intros H s z1 z2. simpl.
    assert (H' : pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub)).
      { apply pub_equiv_merge_states. }
    apply H in H'. rewrite pub_equiv_split_iff in H'.
    unfold pub_equiv_split in H'. apply functional_extensionality. apply H'.
  - intros H s1 s2 Hequiv. simpl in H.
    rewrite pub_equiv_split_iff in Hequiv. unfold pub_equiv_split in Hequiv.
    rewrite pub_equiv_split_iff. unfold pub_equiv_split. intro x.
    specialize (H (split_state s1 pub true)
                  (split_state s1 pub false)
                  (split_state s2 pub false)).
    rewrite merge_states_split_state in H.
    apply functional_extensionality in Hequiv. rewrite Hequiv in H.
    rewrite merge_states_split_state in H.
    rewrite H. reflexivity.
Qed.

(* ################################################################# *)
(** * SME for state transformers *)

(** We can use the [split_state] and [merge_states] functions above to
    also define SME for state transformers. We call the [split_state]
    below to zero out all secret variables before calling [f] the first
    time to obtain the final value of the public variables. *)

Definition sme_state (f : state -> state) (pub:pub_vars) :=
  fun s => merge_states (f (split_state s pub true)) (f s) pub.

(** We will see examples of this in an upcoming section, but for now
    we prove the same two theorems as for [sme] above: *)

Theorem noninterferent_sme_state : forall pub f,
  noninterferent_state pub (sme_state f pub).
Proof.
  unfold noninterferent_state, sme_state.
  intros pub f s1 s2 Hequiv.
  rewrite pub_equiv_split_iff in Hequiv.
  unfold pub_equiv_split in Hequiv.
  apply functional_extensionality in Hequiv. rewrite Hequiv.
  apply pub_equiv_merge_states.
Qed.

Theorem transparent_sme_state : forall f pub,
  noninterferent_state pub f -> forall s, f s = sme_state f pub s.
Proof.
  unfold noninterferent_state, sme_state.
  intros f pub Hni s.
  unfold merge_states, split_state. unfold pub_equiv in Hni.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Eq.
  - apply Hni.
    + intros x' Hx'.
      destruct (Bool.eqb_spec (pub x') true).
      * reflexivity.
      * contradiction.
    + assumption.
  - reflexivity.
Qed.

(** One thing to note in this proof is that we used the lemma
    [Bool.eqb_spec] to do case analysis on whether the [pub x'] is
    equal to [true]. For more details on how this works, please check
    out the explanations about the [reflect] inductive predicate in
    [IndProp]. *)

(* ================================================================= *)
(** ** Optional: Connection between [sme] and [sme_state]  *)

(** We can formally relate [sme] amd [sme_state], but this gets pretty
    technical, so the curious reader can directly skip to the two
    theorems at the end of this subsection. *)

Lemma split_merge_public: forall s pub,
    split_state s pub true = merge_states s (fun _ => 0) pub.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (pub x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma split_merge_split_true: forall s s' pub,
    split_state (merge_states s s' pub) pub true = split_state s pub true.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (pub x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma split_merge_split_false: forall s s' pub,
    split_state (merge_states s s' pub) pub false = split_state s' pub false.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (pub x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma merge_states_same: forall s pub,
    merge_states s s pub = s.
Proof.
  unfold merge_states. intros.
  eapply functional_extensionality. intro x.
  destruct (pub x); reflexivity.
Qed.

Lemma split_state_idem: forall s pub b,
    split_state (split_state s pub b) pub b = split_state s pub b.
Proof.
  unfold split_state. intros.
  eapply functional_extensionality. intro x.
  destruct (Bool.eqb (pub x) b); reflexivity.
Qed.

Lemma eqb_neg_distr_r: forall b1 b2,
    Bool.eqb b1 (negb b2) = negb (Bool.eqb b1 b2).
Proof. intros. destruct b1, b2; simpl; reflexivity. Qed.

Lemma split_state_orthogonal: forall s pub b,
    split_state (split_state s pub b) pub (negb b) = fun _ => 0.
Proof.
  unfold split_state. intros.
  eapply functional_extensionality. intro x.
  rewrite eqb_neg_distr_r.
  destruct (Bool.eqb (pub x) b) eqn:BOOL; simpl; reflexivity.
Qed.

(** First, we show a relationship between [sme] and [sme_state] using [split_state_fun]: *)

Theorem split_sme_state_sme: forall pub f,
    split_state_fun pub (sme_state f pub) = sme (fun _ => 0) (split_state_fun pub f).
Proof.
  intros.
  eapply functional_extensionality. intro PI.
  eapply functional_extensionality. intro SI.
  unfold split_state_fun, sme.
  rewrite pair_equal_spec. split.
  - simpl. unfold sme_state.
    rewrite <- split_merge_public.
    repeat rewrite split_merge_split_true. reflexivity.
  - simpl. unfold sme_state.
    rewrite split_merge_split_false. reflexivity.
Qed.

(** Second, we also show a relationship between [sme] and [sme_state] using merge_state_fun: *)

Definition merge_state_fun (pub : pub_vars) (sf : state -> state -> state*state) :=
  fun s : state =>
    let ps := sf (split_state s pub true) (split_state s pub false) in
    merge_states (fst ps) (snd ps) pub.

Theorem merge_sme_state_sme: forall pub f,
    sme_state (merge_state_fun pub f) pub = merge_state_fun pub (sme (fun _ => 0) f).
Proof.
  intros.
  eapply functional_extensionality. intro s.
  eapply functional_extensionality. intro x.
  unfold merge_state_fun. simpl.
  unfold sme_state. unfold merge_states.
  destruct (pub x) eqn:PUB.
  - rewrite split_state_idem. rewrite split_state_orthogonal. reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Noninterference for Imp programs without loops *)

(** For programs without loops the "failed attempt" evaluation function from
    [Imp] works well and allows us to easily define a state transformer
    function for each Imp command. *)

Print ceval_fun_no_while.
Definition flip {A B C : Type} (f : A -> B -> C) := fun b a => f a b.
Definition cinterp : com -> state -> state := flip ceval_fun_no_while.

Definition noninterferent_no_while pub c : Prop :=
  noninterferent_state pub (cinterp c).

(** A command [c] without loops is noninterferent if the state
    transformer obtained by interpreting the command with [cinterp]
    maps public-equivalent States to public-equivalent states.

    Let's use this definition to prove that the following command is
    noninterferent: *)

Definition xpub : pub_vars := (X !-> true; __ !-> false).

Definition secure_com : com :=
  <{ X := X+1;
     Y := (X-1)+Y*2 }>.

(** For proving [secure_com] noninterferent we first prove a few
    helper lemmas. *)

Lemma xpub_true : forall x, xpub x = true -> x = X.
Proof.
  unfold xpub. intros x Hx.
  destruct (eqb_spec x X).
  - subst. reflexivity.
  - rewrite t_update_neq in Hx.
    + rewrite t_apply_empty in Hx. discriminate.
    + intro contra. subst. contradiction.
Qed.

(** Here we are using the [t_update_neq] and [t_apply_empty] lemmas from [Maps] *)

Lemma xpubX : xpub X = true.
Proof. reflexivity. Qed.

(** Using these lemmas the noninterference proof for [secure_com] is easy: *)

Lemma noninterferent_secure_com :
  noninterferent_no_while xpub secure_com.
Proof.
  unfold noninterferent_no_while, noninterferent_state, secure_com.
  intros s1 s2 PEQUIV x Hx.

  (* Since x is the only public variable in xpub, we know [x = X] *)
  apply xpub_true in Hx. subst.

  (* From public equivalence we show [s1 X = s2 X]. *)
  specialize (PEQUIV X xpubX).

  (* We use computation (running [cinterp]) to show that
     X in [secure_com] depends only on the initial X. *)
  simpl. rewrite PEQUIV. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (noninterferent_secure_ex1) *)
Definition secure_ex1 :=
  <{ Y := Y - 1;
     X := 1 }>.

Lemma noninterferent_secure_ex1 :
  noninterferent_no_while xpub secure_ex1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (noninterferent_secure_ex2) *)
Definition secure_ex2 :=
  <{ if X = 0 then
       X := X + 5
     else
       Y := X
     end }>.

Lemma noninterferent_secure_ex2 :
  noninterferent_no_while xpub secure_ex2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now let's look at a couple of insecure commands: *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := (X-1)+Y*2 }>.

(** An _explicit flow_ is when a command directly assigns an expression
    depending on secret variables to a public variable, like the [X := Y+1]
    assignment above. Explicit flows are easier to find automatically
    and even simple taint-tracking would be enough for discovering this.

    We prove that [insecure_com1] is interferent as follows: *)

Lemma interferent_insecure_com1 :
  ~noninterferent_no_while xpub insecure_com1.
Proof.
  unfold noninterferent_no_while, noninterferent_state, insecure_com1.
  intro Hc.

  (* Choose [s1] and [s2] that are pub_equiv but have different secret inputs. *)
  set (s1 := (X !-> 0 ; Y !-> 0)).
  set (s2 := (X !-> 0 ; Y !-> 1)).
  specialize (Hc s1 s2).

  assert (PEQUIV: pub_equiv xpub s1 s2).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }

  specialize (Hc PEQUIV X xpubX).

  (* Computing reveals that X in [insecure_com1] depends on the initial Y. *)
  simpl in Hc. unfold s1, s2, t_update in Hc. simpl in Hc.

  (* Contradiction: LHS gives X = 1, RHS gives X = 2,
                    but Hc claims they're equal. *)
  discriminate Hc.
Qed.

(** As we saw above, the [set] tactic allows us to give names to
    complex expression, making proofs more readable and
    manageable. It's particularly useful when constructing concrete
    counterexamples where one needs to work with specific values. *)

(** **** Exercise: 2 stars, standard (interferent_insecure_com_explicit) *)
Definition insecure_com_explicit :=
  <{ X := Y + X; (* <- bad explicit flow! *)
     Y := Y - 1 }>.

Lemma interferent_insecure_com_explicit :
  ~noninterferent_no_while xpub insecure_com_explicit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Noninterference can be violated not only by explicit flows, but also by
    _implicit flows_, which leak secret information via the control-flow of the
    program. Here is a simple example: *)

Definition insecure_com2 : com :=
  <{ if Y = 0 then
       Y := 42
     else
       X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public information, but
    we are doing this assignment after we branched on a secret condition [Y =
    0], so we are indirectly leaking information about the value of [Y]. In this
    case we can infer that if [X] gets incremented the value of [Y] is not [0]. *)

Lemma interferent_insecure_com2 :
  ~noninterferent_no_while xpub insecure_com2.
Proof.
  (* The same proof as for [insecure_com1] does the job *)
  unfold noninterferent_no_while, noninterferent_state, insecure_com1.
  intro Hc.

  (* Choose [s1] and [s2] that are pub_equiv but have different secret inputs. *)
  set (s1 := (X !-> 0 ; Y !-> 0)).
  set (s2 := (X !-> 0 ; Y !-> 1)).
  specialize (Hc s1 s2).

  assert (PEQUIV: pub_equiv xpub s1 s2).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }

  specialize (Hc PEQUIV X xpubX).

  (* Computing reveals that X in [insecure_com2] depends on the initial Y. *)
  simpl in Hc. unfold s1, s2, t_update in Hc. simpl in Hc.

  (* Contradiction: LHS gives X = 0, RHS gives X = 1,
                    but Hc claims they're equal. *)
  discriminate Hc.
Qed.

(** **** Exercise: 3 stars, standard (interferent_insecure_com_implicit) *)
Definition insecure_com_implicit :=
  <{ if Y = 42 then
       X := X - 1 (* <- bad implicit flow! *)
     else
       Y := 2 * Y
     end }>.

Lemma interferent_insecure_com_implicit :
  ~noninterferent_no_while xpub insecure_com_implicit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We will return to explicit and implicit flows in the [StaticIFC] chapter. *)

(* ################################################################# *)
(** * SME for Imp programs without loops *)

(** We can use [sme_state] to execute such programs to obtain a
    noninterferent state transformer by running programs 2 times, once
    on a state where the secrets were zeroed out and once on the
    original input state, and then merging the final states. *)

Print sme_state.
(*  fun f pub s => merge_states (f (split_state s pub true)) (f s) pub. *)

Definition sme_cmd c : pub_vars->state->state := sme_state (cinterp c).

(** The result of applying [sme_cmd] to a program is not a program,
    but a state transformer. We prove noninterference and transparency
    for the state transformers obtained by [sme_cmd] using our
    noninterference and transparency theorems about [sme_state]: *)

Theorem noninterferent_sme_cmd : forall c pub,
  noninterferent_state pub (sme_cmd c pub).
Proof. intros c p. apply noninterferent_sme_state. Qed.

Theorem transparent_sme_cmd : forall c pub,
    noninterferent_state pub (fun s => ceval_fun_no_while s c) ->
    forall s, cinterp c s = sme_cmd c pub s.
Proof.
  unfold sme_cmd. intros c pub NI. apply transparent_sme_state. apply NI.
Qed.

(** Perhaps more interesting is to look at how [sme_cmd]
    changes the behavior of some insecure commands: *)

Print insecure_com1. (* <{ X := Y + 1; Y := X - 1 + Y * 2 }> *)
Definition secure_com1 : com :=
  <{ X := 1; (* no explicit flow *)
     Y := Y*3 (* but Y has to be computed in a different way *) }>.

Lemma sme_insecure_com1 : sme_cmd insecure_com1 xpub = cinterp secure_com1.
Proof.
  eapply functional_extensionality. intros st.
  unfold sme_cmd, sme_state, insecure_com1. simpl.
  eapply functional_extensionality. intros x.
  unfold merge_states. simpl.

  destruct (xpub x) eqn:HXP.
  { eapply xpub_true in HXP. subst.
    rewrite t_update_neq; try (intros Hcontra; discriminate).
    rewrite t_update_eq; simpl; auto. }

  destruct (eqb x Y) eqn:HY.
  { rewrite eqb_eq in HY. subst.
    repeat rewrite t_update_eq.
    repeat rewrite t_update_neq; try (intros Hcontra; discriminate).
    lia. }

  assert (HX: x <> X).
  { intros Hx. subst. rewrite xpubX in HXP. discriminate. }

  rewrite eqb_neq in HY.
  repeat (rewrite t_update_neq; auto).
Qed.

(** The example above shows that the effect of applying [sme_cmd] is
    hard to predict statically and it is not just a simple syntactic
    transformation of the original command. Here is another example of that: *)

Definition insecure_com2' : com :=
  <{ if Y = 0 then
       X := 42  (* <- bad implicit flow! *)
     else
       X := X + 1 (* <- bad implicit flow! *)
     end }>.

Definition secure_com2' : com :=
  <{ X := 42 (* <- no implicit flow (no branching) *) }>.

Lemma sme_insecure_com2' : sme_cmd insecure_com2' xpub = cinterp secure_com2'.
Proof.
  eapply functional_extensionality. intros st.
  unfold sme_cmd. unfold sme_state. simpl.
  eapply functional_extensionality. intros x.
  unfold merge_states. simpl.

  destruct (xpub x) eqn:HXP.
  { eapply xpub_true in HXP. subst.
    rewrite t_update_eq; simpl; auto. }

  destruct (eqb x Y) eqn:HY.
  { rewrite eqb_eq in HY. subst.
    destruct (st Y =? 0);
      repeat rewrite t_update_neq;
      try (intros Hcontra; discriminate); reflexivity. }

  assert (HX: x <> X).
  { intros Hx. subst. rewrite xpubX in HXP. discriminate. }

  rewrite eqb_neq in HY.
  destruct (st Y =? 0).
  - rewrite t_update_neq; auto.
  - repeat rewrite t_update_neq; auto.
Qed.

(** For simplicity, above we looked at a modified [insecure_com2'].
    What about the effect of [sme_cmd] on the _original_ [insecure_com2]? *)
Print insecure_com2.
  (* <{ if Y = 0 then *)
  (*      Y := 42  <- updating Y here *)
  (*    else *)
  (*      X := X+1 <- bad implicit flow! *)
  (*    end }>. *)

(** This is more challenging, but it turns out there is a general and
    systematic way to characterize the effect of [sme_cmd] as a single
    program. This program is called a _self-composition_ and it
    captures two executions of the original program (in this case the
    two executions performed by [sme_cmd]): *)

Definition pX := "pX"%string.
Definition pY := "pY"%string.
Definition secure_com2 :=
  <{ (* we save a copy of the initial values of public variables *)
     pX := X;
     (* we run the original program to simulate the secret run *)
     if Y = 0 then Y := 42
              else X := X+1 end; (* <- X later overwritten *)
     (* for the public run we zero the [p]-version of secret variables *)
     pY := 0;
     (* we simulate the effect of the public run using the [p] variables *)
     if pY = 0 then pY := 42
               else pX := pX+1 end; (* <- the branching is on pY *)
     (* we merge the results of the two runs *)
     X := pX
}>.

(** Because in our simple Imp language we have no way to restore the
    [pX] and [pY] variables to their original state, the equivalence
    lemma below needs to account for the fact that their values will be
    different. We do this by reusing our old friend [pub_equiv]: *)

Definition psecret := (pX !-> false; pY !-> false; __ !-> true).

Lemma sme_insecure_com2 : forall st,
    pub_equiv psecret (sme_cmd insecure_com2 xpub st)
                      (cinterp secure_com2 st).
Proof.
  unfold pub_equiv. intros st x PSEC.

  unfold sme_cmd, sme_state, insecure_com2. simpl.
  unfold merge_states. simpl.

  destruct (xpub x) eqn:HXP.
  { eapply xpub_true in HXP. subst.
    rewrite t_update_neq; try discriminate.
    rewrite t_update_eq.
    unfold split_state. simpl.
    repeat (rewrite t_update_neq; try discriminate).
    destruct (st Y =? 0) eqn:HY0.
    - rewrite t_update_neq; try discriminate.
      rewrite t_update_eq. reflexivity.
    - rewrite t_update_neq; try discriminate.
      rewrite t_update_eq. reflexivity. }

  destruct (eqb x Y) eqn:HY.
  { rewrite eqb_eq in HY. subst.
    destruct (st Y =? 0) eqn:HY0.
    - rewrite t_update_eq.
      repeat (rewrite t_update_neq; try discriminate).
      rewrite HY0.
      rewrite t_update_eq. reflexivity.
    - repeat (rewrite t_update_neq; try discriminate).
      rewrite HY0.
      repeat (rewrite t_update_neq; try discriminate).
      reflexivity. }

  rewrite eqb_neq in HY.

  assert (HX: x <> X).
  { intros Hx. subst. rewrite xpubX in HXP. discriminate. }

  assert (HpXY: x <> pX /\ x <> pY).
  { clear - PSEC.
    unfold psecret in PSEC.
    destruct (eqb x pX) eqn:HpX.
    - rewrite eqb_eq in HpX. subst.
      rewrite t_update_eq in PSEC. discriminate.
    - destruct (eqb x pY) eqn:HpY.
      + rewrite eqb_eq in HpY. subst.
        rewrite t_update_neq in PSEC; discriminate.
      + rewrite eqb_neq in HpX. subst.
        rewrite eqb_neq in HpY. subst. auto. }

  destruct HpXY as [HpX HpY].

  repeat (rewrite t_update_neq; auto); try discriminate.
  destruct (st Y =? 0) eqn:HY0.
  - repeat (rewrite t_update_neq; auto).
  - repeat (rewrite t_update_neq; auto).
Qed.

(** By optimizing the self-composition program above quite a bit we
    can finally figure out what [sme_cmd] does for [insecure_com2]: *)

Definition secure_com2_simple :=
  <{ if Y = 0 then
       Y := 42
     else
       skip (* <- implicit flow gone *)
     end
}>.

Lemma sme_insecure_com2_simple :
  sme_cmd insecure_com2 xpub = cinterp secure_com2_simple.
Proof.
  eapply functional_extensionality. intros st.
  unfold sme_cmd. unfold sme_state. simpl.
  eapply functional_extensionality. intros x.
  unfold merge_states. simpl.

  destruct (xpub x) eqn:HXP.
  { eapply xpub_true in HXP. subst.
    rewrite t_update_neq; try discriminate.
    unfold split_state. simpl.
    destruct (st Y =? 0).
    - rewrite t_update_neq; try discriminate.
      reflexivity.
    - reflexivity. }

  destruct (eqb x Y) eqn:HY.
  { rewrite eqb_eq in HY. subst.
    destruct (st Y =? 0).
    - repeat rewrite t_update_eq. reflexivity.
    - rewrite t_update_neq; try discriminate.
      reflexivity. }

  assert (HX: x <> X).
  { intros Hx. subst. rewrite xpubX in HXP. discriminate. }

  rewrite eqb_neq in HY.
  destruct (st Y =? 0).
  - reflexivity.
  - rewrite t_update_neq; auto.
Qed.

(** Self-composition and the more general concept of a _product program_
    are generally useful techniques of their own (e.g., for reducing
    relational properties proved by Relational Hoare Logic to regular
    properties proved by standard Hoare Logic), but we will not
    discuss them here any further. *)

(* ################################################################# *)
(** * Noninterference for Imp programs with loops *)

(** In the presence of loops, we need to define noninterference using the
    evaluation relation ([ceval]) of Imp: *)

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

Ltac invert H := inversion H; subst; clear H.

(** We re-prove noninterference of [secure_com] for this new definition: *)

Lemma noninterferent_secure_com_a_bit_harder :
  noninterferent_while xpub secure_com.
Proof.
  unfold noninterferent_while, secure_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply xpub_true in Hx. subst.
  (* the proof is the same, but with some extra ugly [invert]s *)
  invert H1. invert H4. invert H7.
  invert H2. invert H3. invert H6. simpl.
  rewrite (H X xpubX). reflexivity.
Qed.

(** The advantage of the new definition is that it also says something
    meaningful about programs with while loops. *)

(** For instance, we can prove that [fact_in_coq] from [Imp] does
    not leak the old value of [Y] and [Z] to [X]: *)

Print fact_in_coq.
(* Definition fact_in_coq : com := *)
(*   <{ Z := X;                    *)
(*      Y := 1;                    *)
(*      while Z <> 0 do            *)
(*        Y := Y * Z;              *)
(*        Z := Z - 1               *)
(*      end }>.                    *)

Lemma noninterferent_fact_in_coq :
  noninterferent_while xpub fact_in_coq.
Proof.
  unfold noninterferent_while, fact_in_coq, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply xpub_true in Hx. subst.
  assert (Hs: forall s s', s =[ Z := X; Y := 1; while Z <> 0 do Y := Y * Z; Z := Z - 1 end ]=> s' ->
                      s X = s' X).
  { intros. clear -H0. invert H0. invert H5.
    invert H2. invert H1. simpl in H6.
    remember (Y !-> 1; Z !-> s X; s) as st.
    replace (s X) with (st X); cycle 1.
    { invert Heqst. rewrite t_update_neq; eauto. intros contra.
      discriminate contra. }
    clear -H6.
    remember <{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }> as loopdef
      eqn:Heqloopdef.
    revert Heqloopdef.
    induction H6; intros.
    - discriminate Heqloopdef.
    - discriminate Heqloopdef.
    - discriminate Heqloopdef.
    - discriminate Heqloopdef.
    - discriminate Heqloopdef.
    - reflexivity.
    - invert Heqloopdef.
      rewrite <- IHceval2; eauto.
      invert H6_. invert H5. invert H2. simpl.
      rewrite t_update_neq; cycle 1.
      { intros contra. discriminate contra. }
      rewrite t_update_neq; eauto.
      intros contra. discriminate contra. }
  eapply Hs in H1. eapply Hs in H2. rewrite <- H1, <- H2.
  rewrite (H X xpubX). reflexivity.
Qed.

(* ################################################################# *)
(** * SME for Imp programs with loops *)

(** To define SME in the presence of while loops we also need to use a
    relation, of a similar type to [ceval]: *)

Check ceval : com -> state -> state -> Prop.

Definition sme_while (pub:pub_vars) (c:com) (s s':state) : Prop :=
  exists ps ss, split_state s pub true =[ c ]=> ps /\
    s =[ c ]=> ss /\
    merge_states ps ss pub = s'.

(** To state that sme_eval is secure, we need to generalize our noninterference
    definition, so that we can apply it not only to [ceval], but with
    any evaluation relation, including [sme_while pub]. *)

Definition noninterferent_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  R c s1 s1' ->
  R c s2 s2' ->
  pub_equiv pub s1' s2'.

(** The proof that [while_sme] is noninterferent is as before, but now it relies
    on the determinism of [ceval], which was obvious for state transformer
    functions, but is not obvious for evaluation relations. *)

Check ceval_deterministic : forall (c : com) (st st1 st2 : state),
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.

Theorem noninterferent_while_sme : forall pub c,
  noninterferent_while_R (sme_while pub) pub c.
Proof.
  unfold noninterferent_while_R, sme_while.
  intros pub c s1 s2 s1' s2' H [ps1 [ss1 [H1p [H1s H1m]]]]
                               [ps2 [ss2 [H2p [H2s H2m]]]].
  subst. rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
  apply functional_extensionality in H. rewrite H in H1p.
  rewrite (ceval_deterministic _ _ _ _ H1p H2p).
  apply pub_equiv_merge_states.
Qed.

(** Turns out we can only prove a weak version of transparency for
    noninterferent programs, and this has to do with nontermination
    (more later). *)

(** But first we need a few lemmas:  *)

Lemma pub_equiv_split_state : forall (pub:pub_vars) s,
  pub_equiv pub (split_state s pub true) s.
Proof.
  unfold pub_equiv, split_state.
  intros pub s x Hx. destruct (Bool.eqb_spec (pub x) true).
  - reflexivity.
  - contradiction.
Qed.

Lemma pub_equiv_sym : forall (pub:pub_vars) s1 s2,
  pub_equiv pub s1 s2 ->
  pub_equiv pub s2 s1.
Proof.
  unfold pub_equiv. intros pub s1 s2 H x Hx.
  rewrite H.
  - reflexivity.
  - assumption.
Qed.

Lemma merge_state_pub_equiv : forall pub ss ps,
  pub_equiv pub ss ps ->
  merge_states ps ss pub = ss.
Proof.
  unfold pub_equiv, merge_states.
  intros pub ss ps H. apply functional_extensionality.
  intros x. destruct (pub x) eqn:Heq.
  - rewrite H.
    + reflexivity.
    + assumption.
  - reflexivity.
Qed.

(** More specifically, we can only prove that an [sme_while] execution
    implies a [ceval] execution: *)

Theorem somewhat_transparent_while_sme : forall pub c,
  noninterferent_while pub c ->
  (forall s s', (sme_while pub) c s s' -> s =[ c ]=> s').
Proof.
  unfold noninterferent_while, sme_while.
  intros pub c Hni s s' [ps [ss [Hp [Hs Hm]]]]. subst s'.
    assert(H:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
    specialize (Hni s (split_state s pub true) ss ps H Hs Hp).
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** But we cannot prove the reverse implication, since a command
    terminating when starting in state [s], does not necessarily still
    terminate when starting in state [split_state s pub true], as
    would be needed for proving [sme_while]. *)

(** Yet it seems we can still do most of the things as in the setting
    without while loops, including SME (just not fully transparent).
    So is there anything special about loops and nontermination?

    Yes, there is! Let's look at our noninterference definition again:

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

    It says that for any two _terminating_ executions, if the initial states
    agree on their public variables, then so do the final states. This is
    traditionally called _termination-insensitive_ noninterference (TINI),
    since it doesn't consider nontermination to be observable to an attacker. *)

(** In particular, the following program is _secure_ wrt TINI: *)

Definition termination_leak : com :=
  <{ if Y = 0 then
       Y := 42
     else
       while true do skip end (* <- leak secret by looping *)
     end }>.

(** And we can prove it ... *)

Lemma Y_neq_X : (Y <> X).
Proof. intro contra. discriminate. Qed.

(** We use a lemma that is a homework exercise in Imp: *)
Check loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').

Definition tini_secure_termination_leak :
  noninterferent_while xpub termination_leak.
Proof.
  unfold noninterferent_while, termination_leak, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx. apply xpub_true in Hx.
  subst. specialize (H X xpubX).
  invert H1.
  + invert H8. simpl.
    rewrite (t_update_neq _ _ _ _ _ Y_neq_X).
    invert H2.
    * invert H8. simpl.
      rewrite (t_update_neq _ _ _ _ _ Y_neq_X). assumption.
    * apply loop_never_stops in H8. contradiction.
  + apply loop_never_stops in H8. contradiction.
Qed.

(* ################################################################# *)
(** * Termination-Sensitive Noninterference *)

(** We can give a stronger definition of security that disallows such
    nontermination leaks. It is traditionally called
    _termination-sensitive noninterference_ (TSNI) and it is defined
    as follows: *)

Definition tsni_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1',
  R c s1 s1' ->
  pub_equiv pub s1 s2 ->
  (exists s2', R c s2 s2' /\ pub_equiv pub s1' s2').

(** We can prove that [termination_leak] doesn't satisfy TSNI: *)

Definition tsni_insecure_termination_leak :
  ~tsni_while_R ceval xpub termination_leak.
Proof.
  unfold tsni_while_R, termination_leak.
  intros Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)
                 (Y !-> 42; X !-> 0 ; Y !-> 0)).
  assert (HH : (X !-> 0; Y !-> 0) =[ termination_leak ]=>
               (Y !-> 42; X !-> 0; Y !-> 0)).
  { clear. unfold termination_leak. constructor.
    - reflexivity.
    - constructor. reflexivity. }
  specialize (Hc HH). clear HH.
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H). clear H.
  destruct Hc as [s2' [Hc _]].
  invert Hc.
  - simpl in H4. discriminate.
  - apply loop_never_stops in H5. contradiction.
Qed.

(** More generally, we can prove that TSNI is strictly stronger than TINI
    (noninterferent_while) *)

Lemma tsni_noninterferent : forall pub c,
  tsni_while_R ceval pub c ->
  noninterferent_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Htsni s1 s2 s1' s2' Hequiv H1 H2.
  specialize (Htsni s1 s2 s1' H1 Hequiv).
  destruct Htsni as [s2'' [H2' Hequiv']].
  rewrite (ceval_deterministic _ _ _ _ H2 H2').
  apply Hequiv'.
Qed.

(** The reverse direction of the implication only works for programs that
    always terminate (such as most of our simple examples above). *)

Lemma terminating_noninterferent_tsni: forall pub c,
  (forall s, exists s', s =[ c ]=> s') ->
  noninterferent_while_R ceval pub c ->
  tsni_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Hterminating Hni s1 s2 s1' H Eq.
  destruct (Hterminating s2) as [s2' H'].
  exists s2'; split.
  - assumption.
  - apply Hni with (s1 := s1) (s2 := s2).
    + assumption.
    + assumption.
    + assumption.
Qed.

(** Now for a more interesting use of TSNI: it turns out that
    [sme_while] is transparent for programs satisfying TSNI. *)

Theorem tsni_transparent_while_sme : forall pub c,
  tsni_while_R ceval pub c ->
  (forall s s', s =[ c ]=> s' <-> (sme_while pub) c s s').
Proof.
  unfold tsni_while_R, sme_while.
  intros pub c Hni s s'.
  assert(HH:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
  split.
  - intros H. specialize (Hni s (split_state s pub true) s' H HH).
    destruct Hni as [s'' [Heval Hequiv]].
    exists s''. exists s'. split.
    + assumption.
    + split.
      * assumption.
      * apply merge_state_pub_equiv. assumption.
  - intros [ps [ss [Hp [Hs Hm]]]]. subst s'.
    specialize (Hni s (split_state s pub true) ss Hs HH).
    destruct Hni as [s' [Hp' Hni]].
    rewrite (ceval_deterministic _ _ _ _ Hp Hp').
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** Unfortunately [sme_while] does not _enforce_ TSNI and this is hard
    to fix in our current setting, where programs only return a result
    in the end, a final state, so we had to merge the public and
    secret inputs into a single final state. Instead, SME is commonly
    defined in a setting with interactive IO, in which public outputs
    and secret outputs can be performed independently, during the
    execution [Devriese and Piessens 2010] (in Bib.v). In that setting, it
    does transparently enforce a termination-insensitive version of
    noninterference later research has called Indirect TSNI
    [Ngo et al 2018] (in Bib.v). *)

(* ================================================================= *)
(** ** Optional: Counterexample showing that SME doesn't enforce TSNI *)

(** We build a counterexample command that does not satisfy TSNI and
    for which the same publicly equivalent initial states [s1] and
    [s2] can be used to show that it still does not satisfy TSNI when
    run with [sme_while].

    In particular, we choose [s1] below so that the command terminates
    and so that zeroing out the secret variable Y has no effect on [s1].
    We choose [s2] so that the command loops, which implies that it
    will still loop on [s2] also when executed with [sme_while]. *)

Section TSNICOUNTER.

Definition counter : com := <{ while (Y = 1) do skip end; X := 1 }>.

Definition s1: state := X !-> 0; Y !-> 0; empty_st.
Definition s2: state := X !-> 0; Y !-> 1; empty_st.
Definition s1': state := X !-> 1; s1.

Lemma counter_s1_terminates_s1': s1 =[ counter ]=> s1'.
Proof.
  unfold counter, s1. eapply E_Seq.
  - eapply E_WhileFalse. simpl. reflexivity.
  - eapply E_Asgn. simpl. reflexivity.
Qed.

Lemma counter_s2_loops : forall s2',
  ~ (s2 =[ counter ]=> s2').
Proof.
  unfold counter. intros s2' Hcontra.

  assert (NSTOP: forall s s', s Y = 1 ->
                         s =[ while Y = 1 do skip end ]=> s' ->
                         False).
  { clear. intros.
    remember <{ while Y = 1 do skip end }> as loopdef
             eqn:Heqloopdef.
    generalize dependent H.
    induction H0; try (discriminate Heqloopdef).
    (* E_WhileFalse *)
    - intros HY.
      injection Heqloopdef as H0 H1. subst.
      simpl in H. rewrite HY in H. discriminate H.
    (* E_WhileTrue *)
    - intros HY.
      injection Heqloopdef as H0 H1. subst.
      inversion H0_; subst. eapply IHceval2; eauto. }

  inversion Hcontra; subst. eapply NSTOP in H1; auto.
Qed.

Lemma initial_pub_equiv: pub_equiv xpub s1 s2.
Proof.
  unfold s1, s2, pub_equiv. intros.
  eapply xpub_true in H. subst.
  repeat rewrite t_update_eq. reflexivity.
Qed.

Lemma not_tsni_counter :
  ~ (tsni_while_R ceval xpub counter).
Proof.
  intros Htsni. unfold tsni_while_R in Htsni.
  specialize (Htsni _ _ _ counter_s1_terminates_s1' initial_pub_equiv).
  destruct Htsni as [s2' [D _]].
  eapply counter_s2_loops. eassumption.
Qed.

Lemma sme_counter_s1_terminates_s1' : sme_while xpub counter s1 s1'.
Proof.
  unfold sme_while, counter.
  exists s1', s1'.
  split; [|split].
  - assert (Hsplit: split_state s1 xpub true = s1).
    { unfold split_state, s1, xpub.
      eapply functional_extensionality. intros x.
      destruct (Bool.eqb ((X !-> true; __ !-> false) x) true) eqn: B.
      - reflexivity.
      - destruct (eqb x Y) eqn:HY.
        + rewrite eqb_eq in HY. subst. rewrite t_update_neq.
          * rewrite t_update_eq. reflexivity.
          * intros Hcontra. inversion Hcontra.
        + rewrite eqb_neq in HY.
          destruct (eqb x X) eqn:HX.
          * rewrite eqb_eq in HX. subst.
            rewrite t_update_eq. reflexivity.
          * rewrite eqb_neq in HX.
            rewrite t_update_neq; eauto.
            rewrite t_update_neq; eauto. }
    rewrite Hsplit. eapply counter_s1_terminates_s1'.
  - eapply counter_s1_terminates_s1'.
  - eapply functional_extensionality. intros x.
    unfold merge_states, xpub.
    destruct ((X !-> true; __ !-> false) x); reflexivity.
Qed.

Lemma sme_counter_s2_loops: forall s2',
  ~ (sme_while xpub counter s2 s2').
Proof.
  unfold not, sme_while. intros s2' H.
  destruct H as [ps [ss [A [B C]]]].
  eapply counter_s2_loops. eassumption.
Qed.

Lemma not_tsni_while_sme :
  ~ (tsni_while_R (sme_while xpub) xpub counter).
Proof.
  intros Htsni. unfold tsni_while_R in Htsni.
  specialize (Htsni _ _ _ sme_counter_s1_terminates_s1' initial_pub_equiv).
  destruct Htsni as [s2' [D _]].
  eapply sme_counter_s2_loops. eassumption.
Qed.

End TSNICOUNTER.

(* 2026-01-07 13:37 *)
