(** * WPgen: Weakest Precondition Generator *)

Set Implicit Arguments.
From SLF Require Import WPsem.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In the previous chapter, we have introduced a predicate called [wp] to
    describe the weakest precondition of a term [t] with respect to a given
    postcondition [Q]. The weakest precondition [wp] is characterized by the
    equivalence: [H ==> wp t Q] if and only if [triple t H Q]. We have proved
    "wp-style" reasoning rules, such as
    [wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q].

    In this chapter, we introduce a function, called [wpgen], to "effectively
    compute" the weakest precondition of a term. The value of [wpgen t] is
    defined recursively over the structure of the term [t], and computes a
    formula that is logically equivalent to [wp t]. The fundamental difference
    between [wp] and [wpgen] is that, whereas [wp t] is a predicate that we can
    reason about by "applying" reasoning rules, [wpgen t] is a predicate that we
    can reason about simply by "unfolding" its definition.

    Another key difference between [wp] and [wpgen] is that the formula produced
    by [wpgen] no longer refers to program syntax. In particular, all program
    variables involved in a term [t] appearing in as statement of the form
    [wp t] are replaced with Coq variables when computing [wpgen t]. The
    benefits of eliminating program variables is that formulae produced by
    [wpgen] can be manipulated without the need to simplify substitutions of the
    form [subst x v t2]. Instead, the beta reduction mechanism of Coq will
    automatically perform substitutions for Coq variables.

    The reader might have encountered the term "weakest precondition generators"
    in the past. Such generators take as input a program annotated with all
    function specifications and loop invariants, and produce a set of proof
    obligations that need to be checked in order to conclude that the code
    indeed satisfies its logical annotations. In contrast, the weakest
    preconditions computed by [wpgen] apply to a piece of code coming without
    any specification or invariant.

    At a high level, the introduction of [wpgen] is a key ingredient to
    smoothening the user-experience of conducting interactive proofs in
    Separation Logic. The matter of the present chapter is to show:

    - how to define [wpgen t] as a recursive function that computes in Coq,
    - how to integrate support for the frame rule in this recursive definition,
    - how to carry out practical proofs using [wpgen].

  The rest of the "first pass" section gives a high-level tour of the steps of
  the construction of [wpgen]. The formal definitions and the set up of
  x-tactics follow in the "more details" section. The treatment of local
  functions is presented in the "optional material" section. This chapter is
  probably the most technical of the course. The reader who finds it hard to
  follow through the entire chapter may safely jump to the next chapter at any
  time after completing the "first pass" section. *)

(* ================================================================= *)
(** ** Step 1: [wpgen] as a Recursive Function over Terms *)

(** As first approximation, [wpgen t Q] is defined as a recursive function that
    pattern matches on its argument [t], and produces an appropriate heap
    predicate in each case. The definitions somewhat mimic the reasoning rules
    of [wp]. For example, where the rule [wp_let] asserts the entailment,
    [wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q], the
    definition of [wpgen] is such that [wpgen (trm_let x t1 t2) Q] is, by
    definition, equal to [wpgen t1 (fun v => wpgen (subst x v t2) Q)]. If [t] is
    a function application, [wpgen t Q] asserts that the current state must be
    described by some heap predicate [H] such that [triple t H Q] holds.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x => \[False]
      | trm_app v1 v2 => \exists H, H \* \[triple t H Q]
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
      end.

    To obtain the actual definition of [wpgen], we need to refine the above
    definition in 4 steps.

    In a first step, we modify the definition in order to make it structurally
    recursive. Indeed, in the above the recursive call [wpgen (subst x v t2)] is
    not made to a strict subterm of [trm_let x t1 t2], thus Coq rejects this
    definition as it stands.

    To fix the issue, we change the definition to the form [wpgen E t Q], where
    [E] denotes an association list bindings values to variables. The intention
    is that [wpgen E t Q] computes the weakest precondition for the term
    obtained by substituting all the bindings from [E] in [t]. This term is
    described by the operation [isubst E t] in the soundness proof in the next
    chapter.

    The updated definition looks as follows. Observe how, when traversing
    [trm_let x t1 t2], the context [E] gets extended as [(x,v)::E]. Observe also
    how, when reaching a variable [x], a lookup for [x] into the context [E] is
    performed for recovering the value bound to [x].

    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => \exists H, H \* \[triple (isubst E t) H Q]
      | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
*)

(* ================================================================= *)
(** ** Step 2: [wpgen] Reformulated to Eagerly Match on the Term *)

(** In a second step, we slightly tweak the definition in order to move the
    [fun (Q:val->hprop)] by which the postcondition is taken as argument, to
    place it inside every case of the pattern matching. The idea is to make it
    explicit that [wpgen E t] can be computed without any knowledge of [Q]. In
    the definition shown below, [formula] is a shorthand for the type
    [(val->hprop)->hprop], which is the type [wpgen E t].

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v =>  fun (Q:val->hprop) => Q v
      | trm_var x =>  fun (Q:val->hprop) =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app t1 t2 => fun (Q:val->hprop) =>
                            \exists H, H \* \[triple (isubst E t) H Q]
      | trm_let x t1 t2 => fun (Q:val->hprop) =>
                              wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.

*)

(* ================================================================= *)
(** ** Step 3: [wpgen] Reformulated with Auxiliary Definitions *)

(** In a third step, we introduce auxiliary definitions to improve the
    readability of the output of [wpgen]. For example, we let [wpgen_val v] be a
    shorthand for [fun (Q:val->hprop) => Q v]. Likewise, we let
    [wpgen_let F1 F2] be a shorthand for
    [fun (Q:val->hprop) => F1 (fun v => F2 Q)]. Using these auxiliary
    definitions, the definition of [wpgen] can be reformulated as follows.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v => wpgen_val v
      | trm_var x => wpgen_var E x
      | trm_app t1 t2 => wpgen_app (isubst E t)
      | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      end.

    Each of the auxiliary definitions introduced for [wpgen] comes with a custom
    notation that enables a nice display of the output of [wpgen]. For example,
    the notation [Let' v := F1 in F2] stands for [wpgen_let F1 (fun v => F2)].
    Thanks to this notation, the result of computing [wpgen] on a source term
    [Let x := t1 in t2], which is an Coq expression of type [trm], is a Coq
    expression of type [formula] displayed as [Let' x := F1 in F2].

    Thanks to these auxiliary definitions and pieces of notation, the formula
    that [wpgen] produces as output reads pretty much like the source term
    provided as input. The benefits, illustrated in the first two chapters
    [Basic] and [Repr], is that the proof obligations can be easily
    related to the source code that they arise from. *)

(* ================================================================= *)
(** ** Step 4: [wpgen] Augmented with Support for Structural Rules *)

(** In a fourth step, we refine the definition of [wpgen] in order to equip it
    with inherent support for applications of the structural rules of the logic,
    namely the frame rule and the rule of consequence. To achieve this, we
    consider a well-crafted predicate called [mkstruct], and insert it at the
    head of the output of every call to [wpgen], including all its recursive
    calls. In other words, the definition of [wpgen] thereafter admits the
    following structure.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
                | trm_val v => ...
                | ...
                end).

    Without entering the details at this stage, the predicate [mkstruct] is a
    function of type [formula->formula] that captures the essence of the
    wp-style consequence-frame rule [wp_conseq_frame], presented the previous
    chapter. This rule asserts that [Q1 \*+ H ===> Q2] implies
    [(wp t Q1) \* H ==> (wp t Q2)]. *)

(** This concludes our little journey towards the definition of [wpgen]. For
    conducting proofs in practice, there remains to state lemmas and define
    "x-tactics" to assist the user in the manipulation of the formula produced
    by [wpgen]. Ultimately, the end-user only manipulates CFML's "x-tactics"
    like in the first two chapters, without ever being required to understand
    how [wpgen] is defined.

    The "more details" section goes again through each of the 4 steps presented
    in the above summary, but explaining in details all the Coq definitions
    involved. *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Definition of [wpgen] for Each Term Construct *)

(** The function [wpgen] computes a heap predicate that has the same meaning as
    [wp]. In essence, [wpgen] takes the form of a recursive function that, like
    [wp], expects a term [t] and a postcondition [Q], and produces a heap
    predicate. The function is recursively defined and its result is guided by
    the structure of the term [t]. In essence, the definition of [wpgen] admits
    the following shape:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => ..
      | trm_seq t1 t2 => ..
      | trm_let x t1 t2 => ..
      | trm_var x => ..
      | trm_app t1 t2 => ..
      | trm_fun x t1 => ..
      | trm_fix f x t1 => ..
      | trm_if v0 t1 t2 => ..
      end).

    Our first goal is to figure out how to fill in the dots for each of the term
    constructors. The intention that guides us for filling the dot is the
    soundness theorem for [wpgen], which takes the following form:

      wpgen t Q ==> wp t Q

    This entailment asserts in particular that, if we are able to establish a
    statement of the form [H ==> wpgen t Q], then we can derive from it
    [H ==> wp t Q]. The latter is also equivalent to [triple t H Q]. Thus,
    [wpgen] can be viewed as a practical tool to establish triples. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Values *)

(** Consider first the case of a value [v]. Recall the reasoning rule for values
    in weakest-precondition style. *)

Parameter wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.

(** The soundness theorem for [wpgen] requires the entailment
    [wpgen (trm_val v) Q ==> wp (trm_val v) Q] to hold.

    To satisfy this entailment, according to the rule [wp_val], it suffices to
    define [wpgen (trm_val v) Q] as [Q v].

    Concretely, we fill in the first dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Functions *)

(** Consider the case of a function definition [trm_fun x t]. Recall that the
    [wp] reasoning rule for functions is very similar to that for values. *)

Parameter wp_fun : forall x t1 Q,
  Q (val_fun x t1) ==> wp (trm_fun x t1) Q.

(** So, likewise, we can define [wpgen] for functions and for recursive
    functions as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
*)

(** Observe that we do not attempt to recursively compute [wpgen] over the body
    of the function. Doing so does not harm expressiveness, because the user may
    request the computation of [wpgen] on a local function when reaching the
    corresponding function definition in the proof. In chapter [Wand], we
    will see how to extend [wpgen] to eagerly process local function
    definitions. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Sequence *)

(** Recall the [wp] reasoning rule for a sequence [trm_seq t1 t2]. *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** The intention is for [wpgen] to admit the same semantics as [wp]. We thus
    expect the definition of [wpgen (trm_seq t1 t2) Q] to have a similar shape
    as [wp t1 (fun v => wp t2 Q)].

    We therefore define [wpgen (trm_seq t1 t2) Q] as
    [wpgen t1 (fun v => wpgen t2 Q)]. The definition of [wpgen] is thus extended
    as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Let-Bindings *)

(** The case of let bindings is similar to that of sequences, except that it
    involves a substitution. Recall the [wp] rule: *)

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

(** We fill in the dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...

    One important observation to make at this point is that the function [wpgen]
    is no longer structurally recursive. Indeed, whereas the first recursive
    call to [wpgen] is invoked on [t1], which is a strict subterm of [t], the
    second call is invoked on [subst x v t2], which is not a strict subterm of
    [t].

    It is technically possible to convince Coq that the function [wpgen]
    terminates, yet with great effort. Alternatively, we can circumvent the
    problem altogether by casting the function in a form that makes it
    structurally recursive. Concretely, we will see further on how to add as
    argument to [wpgen] a substitution context, written [E], to delay the
    computation of substitutions until the leaves of the recursion. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Variables *)

(** We have seen no reasoning rules for establishing a triple for a program
    variable, that is, to prove [triple (trm_var x) H Q]. Indeed, [trm_var x] is
    a stuck term: its execution does not produce an output. A source term may
    contain program variables, however all these variables should be substituted
    away before the execution reaches them.

    In the case of the function [wpgen], a variable bound by let-binding get
    substituted while traversing that let-binding construct. Thus, if a free
    variable is reached by [wpgen], it means that this variable was originally a
    dangling free variable, and therefore that the initial source term was
    invalid.

    Although we have presented no reasoning rules for [triple (trm_var x) H Q]
    nor for [H ==> wp (trm_var x) Q], we nevertheless have to provide some
    meaningful definition for [wpgen (trm_var x) Q]. This definition should
    capture the fact that this case must not happen. The heap predicate
    [\[False]] appropriately captures this intention.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_var x => \[False]
      ...
*)

(** Remark: the definition of \[False] translates the fact that, technically, we
    could have stated a Separation Logic rule for free variables, using [False]
    as a premise [\[False]] as precondition. There are three canonical ways of
    presenting this rule, they are shown next. *)

Lemma wp_var : forall x Q,
  \[False] ==> wp (trm_var x) Q.
Proof using. intros. intros h Hh. destruct (hpure_inv Hh). false. Qed.

Lemma triple_var : forall x H Q,
  False ->
  triple (trm_var x) H Q.
Proof using. intros. false. Qed.

Lemma triple_var' : forall x Q,
  triple (trm_var x) \[False] Q.
Proof using. intros. rewrite <- wp_equiv. applys wp_var. Qed.

(** All these rules are correct, albeit totally useless. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Function Applications *)

(** Consider an application in A-normal form, that is, an application of the
    form [trm_app v1 v2]. We have seen [wp]-style rules to reason about the
    application of a known function, e.g. [trm_app (val_fun x t1) v2]. However,
    if [v1] is an abstrat value (e.g., a Coq variable of type [val]), we have no
    reasoning rule at hand that applies. Instead, we expect to reason about an
    application [trm_app v1 v2] by exhibiting a triple of the form
    [triple (trm_app v1 v2) H Q]. Thus, [wpgen (trm_app t1 t2) Q] needs to
    capture the fact that it describes a heap that could also be described by an
    [H] for which [triple (trm_app v1 v2) H Q] holds.

    The formula that formalizes this intuition is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => exists H, H \* \[triple t H Q]
      ...

    Another possibility would be define [wpgen (trm_app t1 t2) Q] as
    [wp (trm_app t1 t2) Q]. In other words, to define [wpgen] for a function
    application, we could fall back to the semantic definition of [wp].

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => wp t Q
      ...

    However, this definition would require converting the [wp] into a [triple]
    each time, because specifications are, by convention, expressed using the
    predicate [triple]. *)

(** Remark: we assume throughout the course that terms are written in A-normal
    form. Nevertheless, we need to define [wpgen] even on terms that are not in
    A-normal form. One possibility is to map all these terms to [\[False]]. In
    the specific case of an application of the form [trm_app t1 t2] where [t1]
    and [t2] are not both values, it is still correct to define
    [wpgen (trm_app t1 t2))] as [wp (trm_app t1 t2)]. So, we need not bother
    checking in the definition of [wpgen] that the arguments of [trm_app] are
    actually values. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Conditionals *)

(** Finally, consider an if-statement. Recall the [wp]-style reasoning rule
    stated using a Coq conditional. *)

Parameter wp_if : forall (b:bool) t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if (val_bool b) t1 t2) Q.

(** Typically, a source program may feature a conditional
    [trm_if (trm_var x) t1 t2] that, after substitution for [x], becomes
    [trm_if (trm_val v) t1 t2], for some abstract [v] of type [val]. Yet, in
    general, this value is now know to be a boolean value. We therefore need to
    define [wpgen] for all if-statements of the form [trm_if (trm_val v0) t1 t2]
    , where [v0] could be a value of unknown shape.

    Yet, the reasoning rule [wp_if] stated above features a right-hand side of
    the form [wp (trm_if (val_bool b) t1 t2) Q]. It only applies when the first
    argument of [trm_if] is syntactically a boolean value [b]. To resolve this
    mismatch, the definition of [wpgen] for a term [trm_if t0 t1 t2] quantifies
    existentially over a boolean value [b] such that [t0 = trm_val (val_bool b)]
    . The formal definition is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Summary of the Definition of [wpgen] for Term Rules *)

(** In summary, we have defined:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_fun x t1 => Q (val_fun x t)
      | trm_fix f x t1 => Q (val_fix f x t)
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      | trm_var x => \[False]
      | trm_app t1 t2 => exists H, H \* \[triple t H Q]
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      end.

    As pointed out earlier, this definition is not structurally recursive and
    thus not accepted by Coq, due to the recursive call [wpgen (subst x v t2) Q]
    . Our next step is to fix this issue. *)

(* ================================================================= *)
(** ** Computing with [wpgen] *)

(** To make [wpgen] structurally recursive, the idea is to postpone the
    substitutions until the leaves of the recursion. To that end, we introduce a
    substitution context, written [E], to record the substitutions that be
    performed. Concretely, we modify the function to take the form [wpgen E t],
    where [E] denotes a list of bindings from variables to values. The intention
    is that [wpgen E t] computes the weakest precondition for the term
    [isubst E t], which denotes the result of substituting all bindings from E
    inside the term [t]. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of Contexts and Operations on Them *)

(** A context [E] is represented as an association list relating variables to
    values. *)

Definition ctx : Type := list (var*val).

(** The "iterated substitution" operation, written [isubst E t], describes the
    substitution of all the bindings form [E] inside a term [t]. Its
    implementation is standard: then function traverses the term recursively
    and, when reaching a variable, performs a lookup in the context [E]. The
    operation needs to take care to respect variable shadowing. To that end,
    when traversing a binder that binds a variable [x], all occurrences of [x]
    that might previously exist in [E] are removed.

    The formal definition of [isubst] involves two auxiliary functions: lookup
    and removal on association lists. The definition of the operation
    [lookup x E] on association lists is standard. It returns an option on a
    value. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** The definition of the removal operation, written [rem x E], is also
    standard. It returns a filtered context. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** The definition of the operation [isubst E t] can then be expressed as a
    recursive function over the term [t]. It invokes [lookup x E] when reaching
    a variable [x]. It invokes [rem x E] when traversing a binding on the name
    [x]. *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  end.

(** Remark: it is also possible to define the substitution by iterating the
    unary substitution [subst] over the list of bindings from [E]. However, this
    alternative approach yields a less efficient function and leads to more
    complicated proofs. *)

(** In what follows, we present the definition of [wpgen E t] case by case.
    Throughout these definitions, recall that [wpgen E t] is interpreted as the
    weakest precondition of [isubst E t]. *)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Let-Binding Case *)

(** When the function [wpgen] traverses a let-binding, rather than eagerly
    performing a substitution, it simply extends the current context.
    Concretely, a call to [wpgen E (trm_let x t1 t2)] triggers a recursive call
    to [wpgen ((x,v)::E) t2]. The corresponding definition is:

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_let x t1 t2 => fun Q =>
           (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Variable Case *)

(** When [wpgen] reaches a variable, it lookups for a binding on the variable
    [x] inside the context [E]. Concretely, the evaluation of
    [wpgen E (trm_var x)] triggers a call to [lookup x E]. If the context [E]
    binds the variable [x] to some value [v], then the operation [lookup x E]
    returns [Some v]. In that case, [wpgen] returns the weakest precondition for
    that value [v], that is, [Q v]. Otherwise, if [E] does not bind [x], the
    lookup operation returns [None]. In that case, [wpgen] returns [\[False]],
    which we have explained to be the weakest precondition for a stuck program.

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_var x => fun Q =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Application Case *)

(** Consider the case of applications. Recall the definition of [wpgen] without
    substitution contexts

   Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ..
      | trm_app t1 t2 => fun Q => exists H, H \* \[triple t H Q]

    In the definition with contexts, the term [t] appearing in [triple t H Q]
    needs to be replaced with [isubst E t].

  Fixpoint wpgen (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_app v1 v2 => fun Q => exists H, H \* \[triple (isubst E t) H Q]
      ..
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Function Definition Case *)

(** Consider the case where [t] is a function definition, for example
    [trm_fun x t1]. Here again, the formula [wpgen E t] is interpreted as the
    weakest precondition of [isubst E t].

    By unfolding the definition of [isubst] in the case where [t] is
    [trm_fun x t1], we obtain [trm_fun x (isubst (rem x E) t1)].

    The corresponding value is [trm_val x (isubst (rem x E) t1)]. The weakest
    precondition for that value is
    [fun Q => Q (val_fun x (isubst (rem x E) t1))].

    Thus, [wpgen E t] handles functions, and recursive functions, as follows:

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_fun x t1 => fun Q => Q (val_fun x (isubst (rem x E) t1))
      | trm_fix f x t1 => fun Q => Q (val_fix f x (isubst (rem x (rem f E)) t1))
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: at Last, an Executable Function *)

Module WpgenExec1.

(** At last, we arrive to a definition of [wpgen] that type-checks in Coq, and
    that can be used to effectively compute weakest preconditions in Separation
    Logic. *)

Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
  match t with
  | trm_val v => Q v
  | trm_fun x t1 => Q (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => Q (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_seq t1 t2 => wpgen E t1 (fun v => wpgen E t2 Q)
  | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
  | trm_var x =>
       match lookup x E with
       | Some v => Q v
       | None => \[False]
       end
  | trm_app v1 v2 => \exists H, H \* \[triple (isubst E t) H Q]
  | trm_if t0 t1 t2 =>
      \exists (b:bool), \[t0 = trm_val (val_bool b)]
        \* (if b then (wpgen E t1) Q else (wpgen E t2) Q)
  end.

(** Compared with the presentation using the form [wpgen t], the new
    presentation using the form [wpgen E t] has the main benefits that it is
    structurally recursive, thus easy to define in Coq. *)

(** Further in the chapter, we will establish the soundness of the [wpgen]. For
    the moment, we simply state the soundness theorem, to explain how it can be
    exploited for verifying concrete programs. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

(** The entailment above asserts in particular that if we can derive
    [triple t H Q] by proving [H ==> wpgen t Q]. A useful corrolary combines the
    soundness theorem with the rule [triple_app_fun], which allows establishing
    triples for functions. Recall the rule [triple_app_fun] from [Rules]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** Reformulating the rule above into a rule for [wpgen] takes 3 steps.

    First, we rewrite the premise [triple (subst x v2 t1) H Q] using [wp]. It
    becomes [H ==> wp (subst x v2 t1) Q].

    Second, we observe that the term [subst x v2 t1] is equal to
    [isubst ((x,v2)::nil) t1]. (This equality is captured by the lemma
    [subst_eq_isubst_one] proved in the bonus section of the chapter.) Thus, the
    heap predicate [wp (subst x v2 t1) Q] is equivalent to
    [wp (isubst ((x,v2)::nil) t1)].

    Third, according to [wpgen_sound], the predicate
    [wp (isubst ((x,v2)::nil) t1)] is entailed by [wpgen ((x,v2)::nil) t1].
    Thus, we can use the latter as premise in place of the former. We thereby
    obtain the following lemma, which is at the heart of the implementation of
    the tactic [xwp]. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Executing [wpgen] on a Concrete Program *)

Import ExamplePrograms.

(** Let us exploit [triple_app_fun_from_wpgen] to demonstrate the computation of
    [wpgen] on a practical program. Recall the function [incr] (defined in
    Rules), and its specification, whose statement appears below. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... *)
Abort.

(** At the ned of the above proof, the goal takes the form [H ==> wpgen body Q],
    where [H] denotes the precondition, [Q] the postcondition, and [body] the
    body of the function [incr]. Observe the invocations of [wp] on the
    application of primitive operations. Observe that the goal is nevertheless
    somewhat hard to relate to the original program. In what follows, we explain
    how to remedy the situation, and set up [wpgen] is such a way that its
    output is human-readable, moreover resembles the original source code. *)

End WpgenExec1.

(* ================================================================= *)
(** ** Optimizing the Readability of [wpgen] Output *)

(** To improve the readability of the formulae produced by [wpgen], we take the
    following 3 steps:

    - first, we modify the presentation of [wpgen] so that the
      [fun (Q:val->hprop) =>] appears insides the branches of the
      [match t with] rather than around it,
    - second, we introduce one auxiliary definition for each branch
      of the [match t with],
    - third, we introduce one piece of notation for each of these
      auxiliary definitions. *)

(* ----------------------------------------------------------------- *)
(** *** Reability Step 1: Moving the Function below the Branches. *)

(** We distribute the [fun Q] into the branches of the [match t]. Concretely, we
    change from:

 Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
   match t with
   | trm_val v     =>  Q v
   | trm_fun x t1  =>  Q (val_fun x (isubst (rem x E) t1))
   ...
   end.

    to the equivalent form:

 Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
   match t with
   | trm_val v     =>  fun (Q:val->hprop) => Q v
   | trm_fun x t1  =>  fun (Q:val->hprop) => Q (val_fun x (isubst (rem x E) t1))
   ...
   end.
*)

(** The result type of [wpgen E t] is [(val->hprop)->hprop]. Thereafter, we let
    [formula] be a shorthand for this type. *)

Definition formula : Type := (val->hprop)->hprop.

(* ----------------------------------------------------------------- *)
(** *** Readability Steps 2 and 3, Illustrated on the Case of Sequences *)

(** We introduce auxiliary definitions to denote the result of each of the
    branches of the [match t] construct. Concretely, we change from:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  fun Q => (wpgen E t1) (fun v => wpgen E t2 Q)
      ...
      end.

    to the equivalent form:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  wpgen_seq (wpgen E t1) (wpgen E t2)
      ...
     end.

    where [wpgen_seq] is defined as shown below. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** Remark: above, [F1] and [F2] denote the results of the recursive calls,
    [wpgen E t1] and [wpgen E t2], respectively.

    With the above definitions, [wgpen E (trm_seq t1 t2)] evaluates to
    [wp_seq (wpgen E t1) (wpgen E t2)]. *)

(** Finally, we introduce a piece of notation for each case. In the case of the
    sequence, we set up the notation defined next to so that any formula of the
    form [wpgen_seq F1 F2] gets displayed as [Seq F1 ; F2 ]. *)

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ';'  '/'  '[' F2 ']' ']'").

(** Thanks to this notation, the [wpgen] of a sequence [t1 ; t2] displays as
    [Seq F1 ; F2] where [F1] and [F2] denote the [wpgen] of [t1] and [t2],
    respectively. *)

(* ----------------------------------------------------------------- *)
(** *** Readability Step 2: Auxiliary Definitions for other Constructs *)

(** We generalize the approach illustrated for sequences to every other term
    construct. The corresponding definitions are stated below. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (t:trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_app (t:trm) : formula := fun Q =>
  \exists H, H \* \[triple t H Q].

(** The new definition of [wpgen] reads as follows. *)

Module WpgenExec2.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

End WpgenExec2.

(* ----------------------------------------------------------------- *)
(** *** Readability Step 3: Notation for Auxiliary Definitions *)

(** We generalize the notation introduced for sequences to every other term
    construct. The corresponding notation is defined below. To avoid conflicts
    with other existing notation, we write [Let'] and [If'] in place of [Let]
    and [If]. *)

Declare Scope wpgen_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69) : wpgen_scope.

Notation "'Let'' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x name, right associativity,
  format "'[v' '[' 'Let''  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'")
  : wpgen_scope.

Notation "'If'' b 'Then' F1 'Else' F2" :=
  ((wpgen_if b F1 F2))
  (at level 69) : wpgen_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69) : wpgen_scope.

(** In addition, we introduce handy notation of the result of [wpgen t] where
    [t] denotes an application. We cover here only functions of arity one or
    two. The file [LibSepReference.v] provides arity-generic definitions. *)

Notation "'App' f v1 " :=
  ((wpgen_app (trm_app f v1)))
  (at level 68, f, v1 at level 0) : wpgen_scope.

Notation "'App' f v1 v2 " :=
  ((wpgen_app (trm_app (trm_app f v1) v2)))
  (at level 68, f, v1, v2 at level 0) : wpgen_scope.

(* ----------------------------------------------------------------- *)
(** *** Test of [wpgen] with Notation. *)

Module WPgenWithNotation.
Import ExamplePrograms WpgenExec2.
Open Scope wpgen_scope.

(** Here again, we temporarily axiomatize the soundness result for the purpose
    of looking at how that result can be exploited in practice. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Consider again the example of [incr]. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... It is of the form [H ==> F Q],
            where [F] vaguely looks like the code of the body of [incr]. *)
Abort.

(** Up to proper tabulation, alpha-renaming, removal of parentheses, and removal
    of quotes after [Let] and [If]), the formula [F] reads as:

      Let n := App val_get p in
      Let m := App (val_add n) 1 in
      App (val_set p) m
*)

(** With the introduction of intermediate definitions for [wpgen] and the
    introduction of associated notations for each term construct, what we
    achieved is that the output of [wpgen] is, for any input term [t], a human
    readable formula whose display closely resembles the syntax source code of
    the term [t]. *)

End WPgenWithNotation.

(* ================================================================= *)
(** ** Extension of [wpgen] to Handle Structural Rules *)

(** The definition of [wpgen] proposed so far integrates the logic of the
    reasoning rules for terms, however it lacks support for conveniently
    exploiting the structural rules of the logic. To improve the situation and
    avoid the need for inductions over terms, we tweak the definition of [wpgen]
    in such a way that, by construction, it satisfies both the frame rule and
    the rule of consequence. *)

(* ----------------------------------------------------------------- *)
(** *** Introduction of [mkstruct] in the Definition of [wpgen] *)

(** The tweak consists of introducing, at every step of the recursion of [wpgen]
    , a special predicate called [mkstruct] to capture the possibility of
    applying structural rules.

    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        match t with
        | trm_val v => wpgen_val v
        ...
        end).

  With this definition, any output of [wpgen E t] is necessarily of the form
  [mkstruct F], for some formula [F] describing the weakest precondition of [t].
  The next step is to investigate what properties [mkstruct] should satisfy. *)

(* ----------------------------------------------------------------- *)
(** *** Properties of [mkstruct] *)

Module MkstructProp.

(** Because [mkstruct] appears between the prototype and the [match] in the body
    of [wpgen], the predicate [mkstruct] must have type [formula->formula]. *)

Parameter mkstruct : formula->formula.

(** The predicate [mkstruct] should satisfy reasoning rules that mimic the
    statements of the frame rule and the consequence rule in
    weakest-precondition style ([wp_frame] and [wp_conseq]). *)

Parameter mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** In addition, the user manipulating a formula produced by [wpgen] should be
    able to discard the predicate [mkstruct] from the head of the output when
    there is no need to apply the frame rule or the rule of consequence. The
    erasure property is captured by the following entailment. *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

(** Moreover, in order to complete the soundness proof for [wpgen], the
    predicate [mkstruct] should be covariant: if [F1] entails [F2], then
    [mkstruct F1] should entail [mkstruct F2]. *)

Parameter mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.

End MkstructProp.

(* ----------------------------------------------------------------- *)
(** *** Realization of [mkstruct] *)

(** The great news is that there exist a predicate satisfying the 4 required
    properties of [mkstruct]. The definition may appears as a piece of magic at
    first. There is no need to understand the definition or the proofs that
    follow. The only piece of useful information here is that there exists a
    predicate [mkstruct] satisfying the required properties. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q1, F Q1 \* (Q1 \--* Q).

(** The magic wand may appear somewhat puzzling, but it fact the above statement
    is reminiscent from the statement of [wp_ramified], which captures the
    expressive power of all the structural reasoning rules of Separation Logic
    at once. If we unfold the definition of the magic wand, we can see more
    clearly that [mkstruct F] is a formula that describes a program that
    produces a postcondition [Q] when executed in the current state if and only
    if the formula [F] describes a program that produces a postcondtion [Q1] in
    a subset of the current state, and if the postcondition [Q1] augmented with
    the remaining of the current state (i.e., the piece described by [H])
    corresponds to the postcondition [Q]. *)

Definition mkstruct' (F:formula) : formula :=
  fun (Q:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q].

(** The 4 properties of [mkstruct] can be easily verified. *)

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using. intros. unfold mkstruct. xpull. intros Q'. xsimpl*. Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using. introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl*. Qed.

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using. intros. unfold mkstruct. xsimpl. Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using. introv WF. unfolds mkstruct. xpull. intros Q'. xchanges WF. Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] that Includes [mkstruct] *)

(** Our final definition of [wpgen] refines the previous one by inserting the
    [mkstruct] predicate to the front of the [match t with] construct. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct (match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end).

(** To avoid clutter in reading the output of [wpgen], we introduce a
    lightweight shorthand to denote [mkstruct F], allowing it to display simply
    as [`F]. *)

Notation "` F" := (mkstruct F) (at level 10, format "` F") : wpgen_scope.

(** Once again, we temporarily axiomatize the soundness result for the purpose
    of looking at how that result can be exploited in practice. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ================================================================= *)
(** ** Lemmas for Handling [wpgen] Goals *)

(** The last major step of the setup of our verification framework consists of
    lemmas and tactics to assist in the processing of formulas produced by
    [wpgen]. For each term construct, and for [mkstruct], we introduce a
    dedicated lemma, called "x-lemma", to help with the elimination of the
    construct. *)

(** [xstruct_lemma] is a reformulation of [mkstruct_erase]. *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

(** [xval_lemma] reformulates the definition of [wpgen_val]. It just unfolds the
    definition. *)

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

(** [xlet_lemma] reformulates the definition of [wpgen_let]. It just unfolds the
    definition. *)

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

(** Likewise, [xseq_lemma] reformulates [wpgen_seq]. *)

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

(** [xapp_lemma] applies to goals produced by [wpgen] on an application. In such
    cases, the proof obligation is of the form [H ==> (wpgen_app t) Q].
    [xapp_lemma] reformulates the frame-consequence rule in a way that enables
    exploiting a specification triple of a function to reason about a call to
    that function. *)

Lemma xapp_lemma : forall t Q1 H1 H2 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wpgen_app t Q.
Proof using.
  introv M WH WQ. unfold wpgen_app. xsimpl. applys* triple_conseq_frame M.
Qed.

(** [xwp_lemma] is another name for [triple_app_fun_from_wpgen]. It is used for
    establishing a triple for a function application. *)

Lemma xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv M1 M2. applys* triple_app_fun_from_wpgen. Qed.

(* ================================================================= *)
(** ** An Example Proof *)

(** Let us illustrate how "x-lemmas" help clarifying verification proof scripts.
    *)

Module ProofsWithXlemmas.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros.
  applys xwp_lemma. { reflexivity. }
  (* Here the [wpgen] function computes. *)
  simpl.
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_add. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_set. } { xsimpl. }
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xlemmas)

    Using x-lemmas, simplify the proof of [triple_succ_using_incr], which was
    carried out using triples in chapter chapter [Rules]. *)

Lemma triple_succ_using_incr_with_xlemmas : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXlemmas.

(* ================================================================= *)
(** ** Making Proof Scripts More Concise *)

(** For each x-lemma, we introduce a dedicated tactic to apply that lemma and
    perform the associated bookkeeping. [xstruct] eliminates the leading
    [mkstruct] that appears in a goal of the form [H ==> mkstruct F Q]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** The tactics [xval], [xseq] and [xlet] invoke the corresponding x-lemmas,
    after calling [xstruct] if a leading [mkstruct] is in the way. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp_nosubst] applys [xapp_lemma], after calling [xseq] or [xlet] if
    applicable. Further on, we will define [xapp] as an enhanced version of
    [xapp_nosusbt] that is able to automatically perform substitutions. *)

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xapp_nosubst" constr(E) :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma E; [ xsimpl | xpull ].

(** [xwp] applys [xwp_lemma], then requests Coq to evaluate the [wpgen]
    function. (For technical reasons, in the definition shown below we need to
    explicitly request the unfolding of [wpgen_var].) *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma;
  [ reflexivity
  | simpl; unfold wpgen_var; simpl ].

(** Let us revisit the previous proof scripts using x-tactics instead of
    x-lemmas. The reader may contemplate the gain in conciseness. *)

Module ProofsWithXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp.
  xapp_nosubst triple_get. intros ? ->.
  xapp_nosubst triple_add. intros ? ->.
  xapp_nosubst triple_set.
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xtactics)

    Using x-tactics, verify the proof of [succ_using_incr]. *)

Lemma triple_succ_using_incr_with_xtactics : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXtactics.

(* ================================================================= *)
(** ** Automated Introductions using the [xapp] Tactic. *)

(** The above proofs frequently exhibit the pattern [intros ? ->] as well as the
    pattern [intros ? x ->] for some variable [x]. This pattern is typically
    occurs whenever the specification of the function being called in the code
    features a postcondition of the form [fun v => \[v = ..]] or of the form
    [fun v => \[v = ..] \* ..]. Let us devise a tactic called [xapp] to
    automatically handle this pattern. The implementation pattern matches on the
    shape of the goal being produced by a call to [xapp_nosubst]. It attempts to
    perform the introduction and the substitution. The reader needs not follow
    through the details of this Ltac definition. *)

Tactic Notation "xapp_try_subst" := (* for internal use only *)
  try match goal with
  | |- forall (r:val), (r = _) -> _ => intros ? ->
  | |- forall (r:val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_nosubst E; xapp_try_subst.

(* ================================================================= *)
(** ** Database of Specification Lemmas for the [xapp] Tactic. *)

(** Explicitly providing arguments to [xapp_nosubst] or [xapp] is tedious. To
    avoid that effort, we set up a database of specification lemmas. Using this
    database, [xapp] can automatically look up for the relevant specification.
    The actual CFML tool uses a proper lookup table binding function names to
    specification lemmas. For this course, however, we'll rely on a simpler
    mechanism, relying on standard hints for [eauto]. In this setting, one can
    register specification lemmas using the [Hint Resolve ... : triple] command,
    as illustrated below. *)

#[global] Hint Resolve triple_get triple_set triple_ref
                       triple_free triple_add : triple.

(** The argument-free variants [xapp_subst] and [xapp] are implemented by
    invoking [eauto with triple] to retrieve the relevant specification.
    DISCLAIMER: the tactic [xapp] that leverages the [triple] database is not
    able to automatically apply specifications that involve a premise that
    [eauto] cannot solve. To exploit such specifications, one need to provide
    the specification explicitly using [xapp E]. *)

Tactic Notation "xapp_nosubst" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma; [ solve [ eauto with triple ] | xsimpl | xpull ].

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

(* ================================================================= *)
(** ** Demo of a Practical Proof using x-Tactics. *)

Module ProofsWithAdvancedXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

(** The tactics defined in the previous sections may be used to complete proofs
    like done in the first two chapters of the course. For example, here is the
    proof of the increment function. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

#[global] Hint Resolve triple_incr : triple.

(** In summary, we have shown how to leverage [wpgen], x-lemmas and x-tactics to
    implement the core of a practical verification framework based on Separation
    Logic. *)

End ProofsWithAdvancedXtactics.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Tactics [xconseq] and [xframe] *)

(** The tactic [xconseq] applies the weakening rule, from the perspective of the
    user, it replaces the current postcondition with a stronger one. Optionally,
    the tactic can be passed an explicit argument, using the syntax [xconseq Q].

    The tactic is implemented by applying the lemma [xconseq_lemma], stated
    below. *)

(** **** Exercise: 1 star, standard, optional (xconseq_lemma)

    Prove the [xconseq_lemma]. *)

Lemma xconseq_lemma : forall Q1 Q2 H F,
  H ==> mkstruct F Q1 ->
  Q1 ===> Q2 ->
  H ==> mkstruct F Q2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xconseq" :=
  applys xconseq_lemma.

Tactic Notation "xconseq" constr(Q) :=
  applys xconseq_lemma Q.

(** The tactic [xframe] enables applying the frame rule on a formula produced by
    [wpgen]. The syntax [xframe H] is used to specify the heap predicate to
    keep, and the syntax [xframe_out H] is used to specify the heap predicate to
    frame out---everything else is kept. *)

(** **** Exercise: 2 stars, standard, optional (xframe_lemma)

    Prove the [xframe_lemma]. Exploit the properties of [mkstruct]; do not try
    to unfold the definition of [mkstruct]. *)

Lemma xframe_lemma : forall H1 H2 H Q Q1 F,
  H ==> H1 \* H2 ->
  H1 ==> mkstruct F Q1 ->
  Q1 \*+ H2 ===> Q ->
  H ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xframe" constr(H) :=
  eapply (@xframe_lemma H); [ xsimpl | | ].

Tactic Notation "xframe_out" constr(H) :=
  eapply (@xframe_lemma _ H); [ xsimpl | | ].

(** Let's illustrate the use of [xframe] on an example. *)

Module ProofsWithStructuralXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr_frame : forall (p q:loc) (n m:int),
  triple (trm_app incr p)
    (p ~~> n \* q ~~> m)
    (fun _ => (p ~~> (n+1)) \* (q ~~> m)).
Proof using.
  xwp.
(** Instead of calling [xapp], we put aside [q ~~> m] and focus on [p ~~> n]. *)
  xframe (p ~~> n). (* equivalent to [xframe_out (q ~~> m)].

    Then we can work in a smaller state that mentions only [p ~~> n]. *)
  xapp. xapp. xapp.
(** Finally we check the check that the current state augmented with the framed
    predicate [q ~~> m] matches with the claimed postcondition. *)
  xsimpl.
Qed.

End ProofsWithStructuralXtactics.

(* ================================================================= *)
(** ** Evaluation of [wpgen] Recursively in Locally Defined Functions *)

Module WPgenRec.
Implicit Types vx vf : val.

(** So far in the chapter, in the definition of [wpgen], we have treated the
    constructions [trm_fun] and [trm_fix] as terms directly constructing a
    value, following the same pattern as for the construction [trm_val].

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v      => Q v
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
      end.

    The present section explains how to extend the definition of [wpgen] to make
    it recurse inside the body of the function definitions. Doing so does not
    increase expressiveness, because the user had the possibility of manually
    requesting the computation of [wpgen] on a function value of the form
    [val_fun] or [val_fix]. However, having [wpgen] automatically recurse into
    function bodies saves the user the need to manually make such requests. In
    short, doing so makes life easier for the end-user. In what follows, we show
    how such a version of [wpgen] can be set up.

    The new definition of [wpgen] will take the shape shown below, for
    well-suited definitions of [wpgen_fun] and [wpgen_fix] yet to be introduced.
    In the code snippet below, [vx] denotes a value to which the function may be
    applied, and [vf] denotes the value associated with the function itself.
    This value is involved where the function defined by [trm_fix f x t1]
    invokes itself recursively inside its body [t1].

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | trm_val v      => wpgen_val v
      | trm_fun x t1   => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      | trm_fix f x t1 => wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)
      ...
      end.
*)

(* ----------------------------------------------------------------- *)
(** *** 1. Treatment of Non-Recursive Functions *)

(** For simplicity, let us assume for now the substitution context [E] to be
    empty and ignore the presence of the predicate [mkstruct]. Our first task is
    to provide a definition for [wpgen (trm_fun x t1) Q], expressed in terms of
    [wpgen t1].

    Let [vf] denote the function [val_fun x t1], which the term [trm_fun x t1]
    evaluates to. The heap predicate [wpgen (trm_fun x t1) Q] should assert that
    that the postcondition [Q] holds of the result value [vf], i.e., that [Q vf]
    should hold.

    Rather than specifying that [vf] is equal to [val_fun x t1] as we were doing
    previously, we would like to specify that [vf] denotes a function whose body
    admits [wpgen t1] as weakest precondition. To that end, we define the heap
    predicate [wpgen (trm_fun x t1) Q] to be of the form
    [\forall vf, \[P vf] \-* Q vf] for a carefully crafted predicate [P] that
    describes the behavior of the function by means of its weakest precondition.
    This predicate [P] is defined further on.

    The universal quantification on [vf] is intended to hide away from the user
    the fact that [vf] actually denotes [val_fun x t1]. It would be correct to
    replace [\forall vf, ...] with [let vf := val_fun x t1 in ...], yet we are
    purposely trying to abstract away from the syntax of [t1], hence the
    universal quantification of [vf].

    In the heap predicate [\forall vf, \[P vf] \-* Q vf], the magic wand
    features a left-hand side of the form [\[P vf]] intended to provide to the
    user the knowledge of the weakest precondition of the body [t1] of the
    function, in such a way that the user is able to derive the specification
    aimed for the local function [vf].

    Concretely, the proposition [P vf] should enable the user establishing
    properties of applications of the form [trm_app vf vx], where [vf] denotes
    the function and [vx] denotes an argument to which the function is applied.

    To figure out the details of the statement of [P], it is useful to recall
    from chapter [WPgen] the statement of the lemma
    [triple_app_fun_from_wpgen], which we used for reasoning about top-level
    functions. *)

Parameter triple_app_fun_from_wpgen : forall vf vx x t1 H' Q',
  vf = val_fun x t1 ->
  H' ==> wpgen ((x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

(** The lemma above enables establishing a triple for an application
    [trm_app vf vx] with precondition [H'] and postcondition [Q'], from the
    premise [H' ==> wgen ((x,vx)::nil) t1 Q'].

    It therefore makes sense, in our definition of the predicate
    [wpgen (trm_fun x t1) Q], which we said would take the form
    [\forall vf, \[P vf] \-* Q vf], to define [P vf] as:

    forall vx H' Q', (H' ==> wpgen ((x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'

    This proposition can be slightly simplified, by using [wp] instead of
    [triple], allowing to eliminate [H']. We thus define [P vf] as:

    forall vx H', wpgen ((x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q'
*)

(** Overall, the definition of [wpgen E t] is as follows. Note that the
    occurence of [nil] is replaced with [E] to account for the case of a
    nonempty context.

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    ...
    | trm_fun x t1 => fun Q =>
       let P vf :=
         (forall vx H', wpgen ((x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q') in
       \forall vf, \[P vf] \-* Q vf
   ...
   end.
*)

(** The actual definition of [wpgen] exploits an intermediate definition called
    [wpgen_fun], as shown below:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      ...
      | trm_fun x t1 => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      ...
      end.

    where [wpgen_fun] is defined as follows: *)

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** Like for other auxiliary functions associated with [wpgen], we introduce a
    custom notation for [wpgen_fun]. Here, we let [Fun x := F] stand for
    [wpgen_fun (fun x => F)]. *)

Notation "'Fun' x ':=' F1" :=
  ((wpgen_fun (fun x => F1)))
  (at level 69, x name, right associativity,
  format "'[v' '[' 'Fun'  x  ':='  F1  ']' ']'").

(* ----------------------------------------------------------------- *)
(** *** 2. Treatment of Recursive Functions *)

(** The formula produced by [wpgen] for a recursive function [trm_fix f x t1] is
    almost the same as for a non-recursive function. The main difference is that
    we need to add a binding in the context from the name [f] to the value [vf].
    Like for [trm_fun], the heap predicate [wpgen (trm_fix f x t1) Q] is of the
    form [\forall vf, \[P vf] \-* Q vf]. The predicate [P] is similar to that
    for [trm_fun], the only difference is that the context [E] needs to be
    extended not with one but with two bindings: one for the argument, and one
    for the function. Concretely, [P] is defined as:

    forall vx H', wpgen ((f,vf)::(x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q'

    To wrap up, to hand recursive functions, we define: *)

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.
(** Then we integrate this definition is [wpgen] as shown below.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | ..
      | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
      | ..
      end
*)
(** Here again, we introduce a piece of notation for [wpgen_fix]. We let
    [Fix f x := F] stand for [wpgen_fix (fun f x => F)]. *)

Notation "'Fix' f x ':=' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (at level 69, f name, x name, right associativity,
  format "'[v' '[' 'Fix'  f  x  ':='  F1  ']' ']'").

(* ----------------------------------------------------------------- *)
(** *** 3. Final Definition of [wpgen], with Processing a Local Functions *)

(** The final definition of [wpgen], including the recursive processing of local
    function definitions, appears below. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_fun (fun v => wpgen ((x,v)::E) t1)
  | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
  | trm_app t1 t2 =>  wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** 4. Tactic for Reasoning About Functions *)

(** Like for other language constructs, we introduce a custom tactic for
    [wpgen_fun]. It is called [xfun], and helps the user to process a local
    function definition in the course of a verification script. The tactic
    [xfun] may be invoked either with or without providing a specification for
    the local function.

 First, we describe the tactic [xfun S], where [S] describes the specification
 of the local function. A typical call is of the form
 [xfun (fun (f:val) => forall ..., triple (f ..) .. ..)]. The tactic [xfun S]
 generates two subgoals. The first one requires the user to establish the
 specification [S] for the function. The second one requires the user to prove
 that the rest of the program is correct, in a context where the local function
 can be assumed to satisfy the specification [S]. The definition of [xfun S]
 appears next. It is not required to understand the details. An example use case
 appears further on. *)

Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.

(** Second, we describe the tactic [xfun] without argument. It applies to a goal
    of the form [H ==> wpgen_fun Fof Q]. The tactic [xfun] simply provides an
    hypothesis about the local function. The user may subsequently exploit this
    hypothesis for reasoning about a call to that function, just like if the
    code of the function was inlined at its call site. In practice, the use of
    [xfun] without argument is most relevant for local functions that are
    invoked exactly once. For example, higher-order iterators such as
    [List.iter] or [List.map] are typically invoked with an ad-hoc functions
    that appears exactly once. *)

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.

(** A generalization of [xfun] that handles recursive functions may be defined
    following exactly the same pattern. Details may be found in the file
    [LibSepReference.v] *)

(** This completes our presentation of a version of [wpgen] that recursively
    processes the local definition of non-recursive functions. An practical
    example is presented next. *)

(* ----------------------------------------------------------------- *)
(** *** 5. Example Computation of [wpgen] in Presence of a Local Function *)

Import DemoPrograms LibSepReference.

(** Consider the following example program, which involves a local function
    definition, then two successive calls to that local function. *)

Definition myfun : val :=
  <{ fun 'p =>
       let 'f = (fun_ 'u => incr 'p) in
       'f ();
       'f () }>.

(** We first illustrate a call to [xfun] with an explicit specification. Here,
    the function [f] is specified as incrementing the reference [p]. Observe
    that the body function of the function [f] is verified only once. The
    reasoning about the two calls to the function [f] that appears in the code
    are done with respect to the specification that we provide as argument to
    [xfun] in the proof script. *)

Lemma triple_myfun : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    triple (f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros.
    applys Hf. (* [Hf] is the name of the hypothesis on the body of [f] *)
    clear Hf.
    xapp. (* exploits [triple_incr] *) xsimpl. }
  xapp. (* exploits [Hf]. *)
  xapp. (* exploits [Hf]. *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

(** We next illustrate a call to [xfun] without argument. The "generic
    specification" that comes as hypothesis about the local function is a
    proposition that describes the behavior of the function in terms of the
    weakest-precondition of its body. When reasoning about a call to the
    function, one can invoke this generic specification. The effect is
    equivalent to that of inlining the code of the function at its call site.
    The example shown below contains two calls to the function [f]. The script
    invokes [xfun] without argument. Then, each of the two calls to [f] executes
    a call to [incr]. Thus the proof script involves two calls to [xapp] that
    each exploit the specification [triple_incr]. *)

Lemma triple_myfun' : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun; intros f Hf.
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

End WPgenRec.

(* ================================================================= *)
(** ** Historical Notes *)

(** Many verification tools based on Hoare Logic are based on a
    weakest-precondition generator. Typically, a tool takes as input a source
    code annotated with specifications and invariants, and produces a logical
    formula that entails the correctness of the program. This logical formula is
    typically expressed in first-order logic, and is discharged using automated
    tools such as SMT solvers.

    In contrast, the weakest-precondition generator presented in this chapter
    applies to un-annotated code. It thus produces a logical formula that does
    not depend at all on the specifications and invariants. Such formula, which
    can be constructed in a systematic manner, is called a "characteristic
    formula" in the literature. In general, a characteristic formula provides
    not just a sound but also a complete description of the semantics of a
    program. Discussion of completeness is beyond the scope of this course.

    The notion of characteristic formula was introduced work by
    [Hennessy and Milner 1985] (in Bib.v) on process calculi. It was first applied to
    program logic by [Honda, Berger, and Yoshida 2006] (in Bib.v). It was then applied
    to Separation Logic in the PhD work of [Charguéraud 2010] (in Bib.v), which
    resulted in the CFML tool.

    CFML 1.0 used an external tool that produced characteristic formulae in the
    form of Coq axioms. Later work by
    [Guéneau, Myreen, Kumar and Norrish 2017] (in Bib.v) showed how the characteristic
    formulae could be produced together with proofs justifying their
    correctness. In 2021, Charguéraud proposed a reformulation of characteristic
    formulae replaced the original presentation based on triples with a simpler
    wp-style presentation. *)

(* 2024-01-03 14:19 *)
