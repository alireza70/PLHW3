(**

Type Soundness in Call-by-value, Simply-typed Lambda Calculus with References

In this homework, you'll prove soundness for a version of the
call-by-value, simply-typed lambda calculus which has been extended to
include references.

Note that in lecture, we used call-by-name, so the semantics here are
slightly different: arguments to functions are evaluated *before* they
are substituted into the function body.

Our language will also include references, which allow provide mutable
updates to variables. References can be allocated with "ref",
dereferenced with "!", and assigned to with "<-". At runtime,
references are represented as "addresses" into a list of terms. As
usual, we will prove that well-typed programs don't get stuck. For
references, this requires that well-typed terms don't contain pointers
to unallocated addresses. We will also require that the type of the
term stored at a given address never changes.

In order to deal with references to the heap, we need to add addresses
(represented in the semantics as (Addr <nat>)). Programmers writing
programs in our language won't write these directly, but when a
reference is allocated with "ref <expr>", the expression is stored in
the heap and the reference expression steps to the address of that
expression.

We encourage you to start early, and to consult the lecture
notes--many of the proofs will be similar to proofs from lecture.

Total points: 120

*)

Require Import List.
Require Import ZArith.
Require Import String.

Open Scope string_scope.

Notation length := List.length.

Ltac inv H := inversion H; subst.

Ltac break_match :=
  match goal with
    | _ : context [ if ?cond then _ else _ ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ if ?cond then _ else _ ] =>
      destruct cond as [] eqn:?
    | _ : context [ match ?cond with _ => _ end ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ match ?cond with _ => _ end ] =>
      destruct cond as [] eqn:?
  end.

(** syntax *)

Inductive expr : Set :=
| Bool   : bool -> expr
| Int    : Z -> expr
| Var    : string -> expr
| App    : expr -> expr -> expr
| Lam    : string -> expr -> expr
| Addr   : nat -> expr
| Ref    : expr -> expr
| Deref  : expr -> expr
| Assign : expr -> expr -> expr.

Coercion Bool : bool >-> expr.
Coercion Int  : Z >-> expr.
Coercion Var  : string >-> expr.

Notation "X @ Y"   := (App X Y)    (at level 49).
Notation "\ X , Y" := (Lam X Y)    (at level 50).
Notation "'ref' X" := (Ref X)      (at level 51).
Notation "! X"     := (Deref X)    (at level 51).
Notation "X <- Y"  := (Assign X Y) (at level 51).

(** Substitution. *)

(** e1[e2/x] = e3 *)
Inductive Subst : expr -> expr -> string ->
                  expr -> Prop :=
| SubstBool:
    forall b e x,
      Subst (Bool b) e x
            (Bool b)
| SubstInt:
    forall i e x,
      Subst (Int i) e x
            (Int i)
| SubstVar_same:
    forall e x,
      Subst (Var x) e x
            e
| SubstVar_diff:
    forall e x1 x2,
      x1 <> x2 ->
      Subst (Var x1) e x2
            (Var x1)
| SubstApp:
    forall e1 e2 e x e1' e2',
      Subst e1 e x e1' ->
      Subst e2 e x e2' ->
      Subst (App e1 e2) e x
            (App e1' e2')
| SubstLam_same:
    forall e1 x e,
      Subst (Lam x e1) e x
            (Lam x e1)
| SubstLam_diff:
    forall e1 x1 x2 e e1',
      x1 <> x2 ->
      Subst e1 e x2 e1' ->
      Subst (Lam x1 e1) e x2
            (Lam x1 e1')
| SubstAddr :
    forall a e x,
      Subst (Addr a) e x
            (Addr a)
| SubstRef :
    forall r e x r',
      Subst r e x r' ->
      Subst (Ref r) e x (Ref r')
| SubstDeref :
    forall r e x r',
      Subst r e x r' ->
      Subst (Deref r) e x (Deref r')
| SubstAssign:
    forall e1 e2 e x e1' e2',
      Subst e1 e x e1' ->
      Subst e2 e x e2' ->
      Subst (Assign e1 e2) e x
            (Assign e1' e2').

(**

[PROBLEM 1 (5 points)]:

  Prove that our substitution relation is deterministic.
  You may find that the f_equal tactic is useful in this proof:
    https://coq.inria.fr/refman/Reference-Manual010.html#hevea_tactic159

 *)
Ltac break_auto := try repeat (break_match || discriminate || intuition).
Ltac h_auto := repeat try ( auto ||
  break_auto || subst || constructor ||
  intros || contradiction || omega
).

Lemma subst_det:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    forall e3',
      Subst e1 e2 x e3' ->
      e3 = e3'.
Proof.
  (* intros. induction H; h_auto. *)
  intros e1 e2 x. induction e1; h_auto; try inv H; h_auto; try inv H0; h_auto.
  -assert (e1' = e1'0). apply IHe1_1 with (e3 := e1') (e3' := e1'0); assumption.
   assert (e2' = e2'0). apply IHe1_2 with (e3 := e2') (e3' := e2'0); assumption.
   subst. econstructor.
  -assert (e1' = e1'0 ). apply IHe1 with (e3 := e1') (e3' := e1'0); assumption.
   subst. econstructor.
  -assert (r' = r'0). apply IHe1 with (e3 := r') (e3' := r'0); assumption.
   subst. econstructor.
 - assert (r' = r'0). apply IHe1 with (e3 := r') (e3' := r'0); assumption. 
   subst. econstructor.
  -assert (e1' = e1'0). apply IHe1_1 with (e3 := e1') (e3' := e1'0); assumption.
   assert (e2' = e2'0). apply IHe1_2 with (e3 := e2') (e3' := e2'0); assumption.
   subst. econstructor.
  Qed. 
(* About 41 tactics *)
(* END PROBLEM 1 *)

(** What does it mean for a variable to be free in an expression?
    There shouldn't be any surprises here, since references don't 
    affect whether a variable is bound or not.
 *)
Inductive free : expr -> string -> Prop :=
| FreeVar:
    forall x,
      free (Var x) x
| FreeApp_l:
    forall x e1 e2,
      free e1 x ->
      free (App e1 e2) x
| FreeApp_r:
    forall x e1 e2,
      free e2 x ->
      free (App e1 e2) x
| FreeLam:
    forall x1 x2 e,
      free e x1 ->
      x1 <> x2 ->
      free (Lam x2 e) x1
| FreeRef :
    forall x r,
      free r x ->
      free (Ref r) x
| FreeDeref :
    forall x r,
      free r x ->
      free (Deref r) x
| FreeAssign_l:
    forall x e1 e2,
      free e1 x ->
      free (Assign e1 e2) x
| FreeAssign_r:
    forall x e1 e2,
      free e2 x ->
      free (Assign e1 e2) x.

(* If a variable isn't free in an expression, 
   substituting that variable doesn't change the expression. *)

Lemma subst_only_free:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    ~ free e1 x ->
    e1 = e3.
Proof.
  induction 1; intros; auto.
  - destruct H. constructor.
  - f_equal.
    + apply IHSubst1; intuition.
      apply H1; apply FreeApp_l; auto.
    + apply IHSubst2; intuition.
      apply H1; apply FreeApp_r; auto.
  - rewrite IHSubst; auto.
    intuition. apply H1.
    constructor; auto.
  - rewrite IHSubst; auto.
    intuition. apply H0.
    constructor; auto.
  - rewrite IHSubst; auto.
    intuition. apply H0.
    constructor; auto.
  - f_equal.
    + apply IHSubst1; intuition.
      apply H1; apply FreeAssign_l; auto.
    + apply IHSubst2; intuition.
      apply H1; apply FreeAssign_r; auto.
Qed.

(** Closed terms have no free variables *)
Definition closed (e: expr) : Prop :=
  forall x, ~ free e x.

(* These are a bunch of boring facts about closed terms. 
   We've completed the proofs, but look over them because 
   they are will be useful later.
 *)
Lemma closed_app_intro:
  forall e1 e2,
    closed e1 ->
    closed e2 ->
    closed (e1 @ e2).
Proof.
  unfold closed, not; intros.
  inv H1.
  -  eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma closed_app_inv:
  forall e1 e2,
    closed (e1 @ e2) ->
    closed e1 /\ closed e2.
Proof.
  unfold closed, not; split; intros.
  - eapply H; eauto.
    apply FreeApp_l; eauto.
  - eapply H; eauto.
    apply FreeApp_r; eauto.
Qed.

Lemma closed_lam_intro:
  forall x e,
    (forall y, y <> x -> ~ free e y) ->
    closed (\x, e).
Proof.
  unfold closed, not; intros.
  inv H0. eapply H; eauto.
Qed.

Lemma closed_lam_inv:
  forall x e,
    closed (\x, e) ->
    (forall y, y <> x -> ~ free e y).
Proof.
  unfold closed, not; intros.
  cut (free (\x, e) y); intros.
  - eapply H; eauto.
  - constructor; auto.
Qed.

Lemma closed_ref_intro:
  forall e,
    closed e ->
    closed (ref e).
Proof.
  unfold closed, not; intros.
  inv H0. eauto.
Qed.

Lemma closed_ref_inv:
  forall e,
    closed (ref e) ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply H. 
  constructor. eauto.
Qed.

Lemma closed_deref_intro:
  forall e,
    closed e ->
    closed (! e).
Proof.
  unfold closed, not; intros.
  inv H0. eauto.
Qed.

Lemma closed_deref_inv:
  forall e,
    closed (! e) ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply H. 
  constructor. eauto.
Qed.

Lemma closed_assign_intro:
  forall e1 e2,
    closed e1 ->
    closed e2 ->
    closed (e1 <- e2).
Proof.
  unfold closed, not; intros.
  inv H1.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma closed_assign_inv:
  forall e1 e2,
    closed (e1 <- e2) ->
    closed e1 /\ closed e2.
Proof.
  unfold closed, not; split; intros.
  - eapply H; eauto.
    apply FreeAssign_l; eauto.
  - eapply H; eauto.
    apply FreeAssign_r; eauto.
Qed.

(**

[PROBLEM 2 (5 points)]: 

  Prove that closed-ness is preserved by substitution.
  This proof should use many of the lemmas defined above.

 *)
Lemma subst_pres_closed:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    closed e1 ->
    closed e2 ->
    closed e3.
Proof.
  -intros. assert ( e1= e3).  apply (@subst_only_free e1 e2 x e3). assumption.
   apply H0 with (x :=x). subst. assumption.
Qed.
(* END PROBLEM 2 *)


(*

Here we define "heaps", which our references will index into.

A heap is just a list of expressions (in our uses later below,
they will always be values) which can be indexed into.

*)

Definition heap := list expr.

(*

We define lookup in terms of the "nth" function:
  https://coq.inria.fr/library/Coq.Lists.List.html

nth takes a default argument (consider why!), but
we will not actually end up in the default case
in our code later below.

*)

Definition lookup (h : heap) n :=
  nth n h true.

(* snoc is cons, backwards. It adds an element to the end of a list. *)
Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
  match l with
    | nil => x :: nil
    | h :: t => h :: snoc t x
  end.

(** We will need some boring lemmas about [snoc]. We've completed the
proofs for you, but look over them since you'll need them later.  *)

Lemma length_snoc : forall A (l:list A) n,
  length (snoc l n) = S (length l).
Proof.
  induction l; intros; auto.
  simpl. rewrite IHl. auto.
Qed.

Lemma nth_lt_snoc : forall A (l:list A) x d n,
  n < length l ->
  nth n l d = nth n (snoc l x) d.
Proof.
  induction l; intros; simpl in *.
  - omega.
  - break_match; auto.
    apply IHl. omega.
Qed.

Lemma nth_eq_snoc : forall A (l:list A) x d,
  nth (length l) (snoc l x) d = x.
Proof.
  induction l; intros; auto.
  simpl. rewrite IHl. auto.
Qed.

(** To update the heap, we use the [replace] function, which replaces
    the contents of a cell at a particular index. *)

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t => 
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(** Of course, we also need some boring lemmas about [replace], which
    are also fairly straightforward to prove. *)

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A (l:list A) n x,
  length (replace n x l) = length l.
Proof.
  induction l; intros; simpl;
  destruct n; simpl; eauto.
Qed.

Lemma lookup_replace_eq : forall h a t,
  a < length h -> 
  lookup (replace a t h) a = t.
Proof.
  unfold lookup.
  induction h; intros; simpl in *; auto.
  - omega.
  - destruct a0; simpl; auto.
    apply IHh. omega.
Qed.

(**

[PROBLEM 3 (5 points)]:

  Prove that replacing a value in a heap doesn't 
  affect lookups for different values.

 *)

Lemma lookup_replace_neq : forall h a1 a2 t,
  a1 <> a2 ->
  lookup (replace a1 t h) a2 = lookup h a2.
Proof.
  intros h. unfold lookup.  
  induction h; intuition.
    +assert (replace a1 t nil = nil). apply replace_nil. rewrite H0.  reflexivity.
    + destruct a1. unfold replace. 
      - destruct a2. intuition. simpl. auto.
      - assert (replace (S a1) t (a::h) = a :: replace a1 t h). constructor. rewrite H0.
        destruct a2. 
        * simpl. auto. 
        * simpl. apply IHh with (a1 := a1 ) (a2 := a2) (t := t). auto. 
Qed.
(* END PROBLEM 3 *)


(*

Now that we have heaps, let's define our semantics!

Since we're writing a call-by-value semantics, 
we first need to define "values".

*)
Inductive isValue : expr -> Prop :=
| VLam  : forall x e, isValue (\ x, e)
| VInt  : forall i : Z, isValue i
| VBool : forall b : bool, isValue b
| VAddr : forall n, isValue (Addr n).

(*

Our step relation includes heaps as well as expressions, since heaps
can change. Look carefully over this step relation and make sure you
understand every rule!  Really, you'll need to grok this to finish the
homework.

*)
Inductive step_cbv : heap -> expr -> heap -> expr -> Prop :=
| SAppLeft :
    forall h h' e1 e1' e2,
      step_cbv h e1
               h' e1' ->
      step_cbv h (e1 @ e2)
               h' (e1' @ e2)
| SAppRight :
    forall h h' e1 e2 e2',
      isValue e1 ->
      step_cbv h e2
               h' e2' ->
      step_cbv h (e1 @ e2)
               h' (e1 @ e2')
| SApp :
    forall h x e1 e2 e1',
      isValue e2 ->
      Subst e1 e2 x e1' ->
      step_cbv h ((\ x, e1) @ e2)
               h e1'
| SRef :
    forall h h' e e',
      step_cbv h e
               h' e' ->
      step_cbv h (ref e)
               h' (ref e')
| SRefValue :
    forall h e,
      isValue e ->
      step_cbv h (ref e)
               (snoc h e) (Addr (length h))
| SDeref :
    forall h h' e e',
      step_cbv h e
               h' e' ->
      step_cbv h (! e)
               h' (! e')
| SDerefAddr :
    forall h a,
      a < length h ->
      step_cbv h (! (Addr a))
               h (lookup h a)
| SAssignLeft :
    forall h h' e1 e1' e2,
      step_cbv h e1
               h' e1' ->
      step_cbv h (e1 <- e2)
               h' (e1' <- e2)
| SAssignRight :
    forall h h' e1 e2 e2',
      isValue e1 ->
      step_cbv h e2
               h' e2' ->
      step_cbv h (e1 <- e2)
               h' (e1 <- e2')
| SAssign :
    forall h a e,
      isValue e ->
      a < length h ->
      step_cbv h (Addr a <- e)
               (replace a e h) (Bool true).

Notation "h1 ; e1 '==>' h2 ; e2" :=
  (step_cbv h1 e1 h2 e2) (at level 40, e1 at level 39, h2 at level 39).

(* any number of steps *)
Inductive star_cbv : heap -> expr -> heap -> expr -> Prop :=
| scbn_refl:
    forall h e,
      star_cbv h e h e
| scbn_step:
    forall h1 e1 h2 e2 h3 e3,
      step_cbv h1 e1 h2 e2 ->
      star_cbv h2 e2 h3 e3 ->
      star_cbv h1 e1 h3 e3.

Notation "h1 ; e1 ==>* h2 ; e2" :=
  (star_cbv h1 e1 h2 e2) (at level 40, e1 at level 39, h2 at level 39).

(* Let's talk about types! *)

(* We'll need to add a type for references to the set of types we saw lecture. *)

Inductive typ : Set :=
| TBool : typ
| TInt  : typ
| TFun  : typ -> typ -> typ
| TRef  : typ -> typ.

Notation "X ~> Y" := (TFun X Y) (at level 60).

(* An environment maps variables to types. Make sure you understand
the difference between this and a heap, which maps indices to
terms! *)

Definition env : Type :=
  string -> option typ.

(* E0 is the empty environment *)
Definition E0 : env :=
  fun _ => None.

(*

Update an environment with a new variable and type.

NOTE: Environments are different from heaps!
      We change heaps with snoc and replace.
      We change environments with extend.

*)
Definition extend (e: env) x t : env :=
  fun y =>
    if string_dec y x then
      Some t
    else
      e y.

(* In addition to our usual environments,
   we also need to type our heaps in order
   to type references. *)

(* A heap type is just a list of types. *)
Definition heap_typ :=
  list typ.

(* lookup_typ works just like lookup. *)
Definition lookup_typ (h : heap_typ) n :=
  nth n h TBool.

(* What does it mean for a term to be well-typed?
   The first 5 constructors are the same as those
   in the STLC without references.
*)

Inductive typed : env -> heap_typ -> expr -> typ -> Prop :=
| WTBool :
    forall env ht b,
      typed env ht (Bool b) TBool
| WTInt :
    forall env ht i,
      typed env ht (Int i) TInt
| WTVar :
    forall env ht x t,
      env x = Some t ->
      typed env ht (Var x) t
| WTApp :
    forall env ht e1 e2 tA tB,
      typed env ht e1 (tA ~> tB) ->
      typed env ht e2 tA ->
      typed env ht (e1 @ e2) tB
| WTLam :
    forall env ht x e tA tB,
      typed (extend env x tA) ht e tB ->
      typed env ht (\x, e) (tA ~> tB)
| WTAddr :
    forall env ht a,
      a < length ht ->
      typed env ht (Addr a) (TRef (lookup_typ ht a))
| WTRef :
    forall env ht e t,
      typed env ht e t ->
      typed env ht (ref e) (TRef t)
| WTDeref :
    forall env ht e t,
      typed env ht e (TRef t) ->
      typed env ht (! e) t
| WTAssign :
    forall env ht e1 e2 t,
      typed env ht e1 (TRef t) ->
      typed env ht e2 t ->
      typed env ht (e1 <- e2) TBool.

(* Q: What does it mean for a heap to be well-typed?

   A: The heap must be the same length as the heap type, and the term
      stored at any valid address in the heap (i.e. any address less than
      the length of the heap) should have the type it has in the heap type.
 *)

Definition heap_typed (ht : heap_typ) (h : heap) :=
  length h = length ht /\
  forall a,
    a < length h ->
    typed E0 ht (lookup h a) (lookup_typ ht a).

(** We want to prove soundness. As usual, we'll prove *progress* and
*preservation*. We'll start with progress, since it's easier. *)


(** In our calculus, a number of types have canonical forms: if a
member of that type is a value, it must have a particular form. These
will be useful in proving progress. *)

Lemma canon_bool:
  forall env ht e,
    isValue e ->
    typed env ht e TBool ->
    exists b, e = Bool b.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_int:
  forall env ht e,
    isValue e ->
    typed env ht e TInt ->
    exists i, e = Int i.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_fun:
  forall env ht e tA tB,
    isValue e ->
    typed env ht e (tA ~> tB) ->
    exists x, exists b, e = \x, b.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_ref:
  forall env ht e t,
    isValue e ->
    typed env ht e (TRef t) ->
    exists a, e = Addr a.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

(* We can always substitute. You'll destruct the value of can_subst on
particular arguments somewhere in the progress proof. *)
Lemma can_subst:
  forall e1 e2 x,
    exists e3, Subst e1 e2 x e3.
Proof.
  induction e1; intros.
  - econstructor; constructor.
  - econstructor; constructor.
  - case (string_dec x s); intros.
    + subst. econstructor; constructor.
    + econstructor; constructor; auto.
  - edestruct IHe1_1; edestruct IHe1_2.
    econstructor; econstructor; eauto.
  - edestruct IHe1.
    case (string_dec x s); intros.
    + subst. econstructor; constructor.
    + econstructor; constructor; eauto.
  - eexists; econstructor.
  - edestruct IHe1; eexists; constructor; eauto.
  - edestruct IHe1; eexists; constructor; eauto.
  - edestruct IHe1_1; edestruct IHe1_2.
    eexists; constructor; eauto.
Qed.

(**

[PROBLEM 4 (30 points)]:

Prove progress for our calculus: given a well-typed heap, a well-typed
sterm can either step or is a value.  We've started the proof for you.

*)
Lemma progress:
  forall ht h e t,
    typed E0 ht e t ->
    heap_typed ht h ->
    (exists e' h', h; e ==> h'; e') \/ isValue e.
Proof.
  (* About 90 tactics *)
  remember E0.
  induction 1; subst; intros.
  - assert (isValue b).  constructor.  intuition.
  -assert(isValue i). constructor. intuition.
  -assert (isValue x). inversion H. unfold E0 in H.  inversion H. 
  - destruct IHtyped1; try auto. inversion H2. inversion H3. 
    assert ( h; (e1 @ e2) ==> x0 ; (x@e2)). econstructor. auto. left. 
    eexists. eexists. apply H5. destruct IHtyped2. auto. auto. inversion H3. inversion H4.
    left.    eexists. eexists. assert (h; (e1 @ e2) ==> x0 ; (e1 @ x)). constructor.
    auto. auto. apply H6. admit. 
 -right. econstructor.
 -right. constructor.
 - destruct IHtyped. auto. auto. inversion H1. inversion H2. left. eexists. eexists.
   assert (h; (ref e) ==> x0 ; (ref x)). constructor. auto. apply H4. 
   assert (h; (ref e) ==> (snoc h e) ;(Addr (length h)) ). constructor.
   auto. left. eexists. eexists. apply H2.
    
 - destruct IHtyped. auto. auto. inversion H1. inversion H2. left. assert (h ; (!e) ==> x0; (!x)).
   constructor. auto. eexists. eexists. apply H4. 
   inversion H1; inversion H; h_auto. inversion H6.
   assert (length ht = length h). unfold heap_typed in H0. destruct H0. auto.
   rewrite H2 in H7. rewrite <- H3. eexists. eexists. 
   apply SDerefAddr with (h := h) (a :=a). auto.  
 - destruct IHtyped1. auto. auto. inversion H2. inversion H3. 
   left. assert ( h; (e1 <- e2) ==> x0; (x <- e2)). constructor. auto.
   eexists. eexists. apply H5. destruct IHtyped2. auto. auto.
   inversion H3. inversion H4. assert (h; (e1 <- e2) ==> x0 ; (e1 <- x)).
   constructor. auto. auto. left. eexists. eexists. apply H6.
   inversion H2; inversion H; h_auto. admit.
 
    
(* END PROBLEM 4 *)

(*

Next, we'll prove preservation. This is going to be a little harder;
we're going to need to develop some machinery around environments and
heap types.

*)

(* Equivalence of environments *)
Definition env_equiv (e1 e2: env) : Prop :=
  forall s, e1 s = e2 s.

(* Some lemmas about this equivalence relation. *)

(* reflexivity *)
Lemma env_equiv_refl:
  forall env,
    env_equiv env env.
Proof.
  unfold env_equiv; auto.
Qed.

(* symmetry *)
Lemma env_equiv_sym:
  forall e1 e2,
    env_equiv e1 e2 ->
    env_equiv e2 e1.
Proof.
  unfold env_equiv; auto.
Qed.

(* transitivity *)
Lemma env_equiv_trans:
  forall e1 e2 e3,
    env_equiv e1 e2 ->
    env_equiv e2 e3 ->
    env_equiv e1 e3.
Proof.
  unfold env_equiv; intros.
  congruence.
Qed.

(* extending environments with the same value preserves equivalence *)
Lemma env_equiv_extend:
  forall env1 env2 x t,
    env_equiv env1 env2 ->
    env_equiv (extend env1 x t) (extend env2 x t).
Proof.
  unfold env_equiv, extend; intros.
  break_match; auto.
Qed.

(* if we extend twice with the same variable, it's equivalent to just
extending with the second value (i.e. we "overwrite" values *)
Lemma env_equiv_overwrite:
  forall env x t1 t2,
    env_equiv (extend (extend env x t1) x t2)
              (extend env x t2).
Proof.
  unfold env_equiv, extend; intros.
  break_match; auto.
Qed.

(* If we extend twice with different variables,
   both possible orders result in equivalent envs.
*)
Lemma env_equiv_neq:
  forall env1 env2 x1 t1 x2 t2,
    x1 <> x2 ->
    env_equiv env1 env2 ->
    env_equiv (extend (extend env1 x1 t1) x2 t2)
              (extend (extend env2 x2 t2) x1 t1).
Proof.
  unfold env_equiv, extend; intros.
  break_match; break_match; congruence.
Qed.

(**

[PROBLEM 5 (5 points)]:

  Prove that if a term is typed in an environment, 
  it's typed in equivalent environments.

*)
Lemma env_equiv_typed:
  forall env1 ht e t,
    typed env1 ht e t ->
    forall env2,
      env_equiv env1 env2 ->
      typed env2 ht e t.
Proof.
  induction 1; h_auto.
  -unfold env_equiv in H0. assert (env0 x = env2 x). apply H0  with (s := x).
   rewrite H in H1. auto.
  -assert (typed env2 ht e1 (tA ~> tB)). apply IHtyped1. auto.
   assert (typed env2 ht e2 tA). apply IHtyped2. auto. econstructor. apply H2. auto.
  -assert (env_equiv  (extend env0 x tA) (extend env2 x tA)). apply env_equiv_extend.
   auto. apply IHtyped with (env2 := (extend env2 x tA)). auto.
  - econstructor. assert (typed env2 ht e1 (TRef t)). apply IHtyped1 with (env2 := env2).
    auto. apply H2. apply IHtyped2 with (env2 := env2). auto.
  (* About 24 tactics *)
Qed.
(* END PROBLEM 5 *)

(*

Weakening is a structural property of environments: it means that if a
term has some type in an environment, then the term still has that
type if we extend the environment with a new value for any variable
that is free in the term. It's called "weakening" because we can prove
that a term has a type in one environment by removing bindings from
another environment where we know the term is typable.

*)

(*

[PROBLEM 6 (10 points)]:

  Prove weakening for environments.

*)
Lemma weaken:
  forall env ht e t,
    typed env ht e t ->
    forall x t',
      ~ free e x ->
      typed (extend env x t') ht e t.
Proof.
  induction 1. 
  -  h_auto. 
  - h_auto. 
  - admit.
  -  intuition. assert (free e1 x -> False). intuition. assert (free (e1 @ e2) x ).
     constructor. auto. apply H1. auto. assert (free e2 x -> False).
     intuition. assert (free (e1 @ e2) x) .  apply FreeApp_r. auto. apply H1.
     auto.  econstructor. eapply IHtyped1. auto. eapply IHtyped2. auto.
  - h_auto. assert (x = x0 \/ ( (x <> x0) /\(free e x0 -> False))). h_auto.  admit.
    destruct H1. rewrite <- H1.  assert ( env_equiv (extend (extend env0 x t') x tA) 
    (extend env0 x tA)). apply (@env_equiv_overwrite env0 x t' tA ). apply (@env_equiv_typed
     (extend env0 x tA) ht e tB ) . auto. apply env_equiv_sym. auto. destruct H1.
    assert (env_equiv (extend (extend env0 x tA) x0 t') (extend (extend env0 x0 t') x tA)).
    apply env_equiv_neq. assumption. apply env_equiv_refl. 
    eapply (@env_equiv_typed (extend (extend env0 x tA) x0 t') ht e tB).
    apply IHtyped. auto. auto.
  -intuition. h_auto.
  -intuition. h_auto. apply IHtyped with (x := x) (t' := t'). intuition. assert (free (ref e) x).
   constructor. auto. apply H0. auto.
  -intuition. h_auto. apply IHtyped with (x := x) (t' := t'). intuition. assert (free (!e) x).
   constructor. auto. apply H0. auto.
  -intuition. h_auto. assert (free e1 x -> False). intuition.  assert (free (e1 <- e2) x).
   constructor. auto. apply H1. auto. 
   assert (free e2 x -> False). intuition.  assert (free (e1 <- e2) x).
   apply FreeAssign_r.  auto.  apply H1. auto. econstructor. apply IHtyped1. auto.
   apply IHtyped2. auto.

Qed.
(* END PROBLEM 6 *)

(* Next, we'll define another notion of equivalence: equivalence of
environments with respect to the free variables in a particular
term. If two environments have the same value for every free variable
in a term, then those environments should be interchangeable when
typing that term. *)

Definition free_env_equiv (E: expr) (e1 e2: env) : Prop :=
  forall x,
    free E x ->
    e1 x = e2 x.

(* We'll prove all the same thigs about this equivalence relation *)
Lemma free_env_equiv_refl:
  forall E env,
    free_env_equiv E env env.
Proof.
  unfold free_env_equiv; auto.
Qed.

Lemma free_env_equiv_sym:
  forall E e1 e2,
    free_env_equiv E e1 e2 ->
    free_env_equiv E e2 e1.
Proof.
  unfold free_env_equiv; intros.
  symmetry. apply H; auto.
Qed.

Lemma free_env_equiv_trans:
  forall E e1 e2 e3,
    free_env_equiv E e1 e2 ->
    free_env_equiv E e2 e3 ->
    free_env_equiv E e1 e3.
Proof.
  unfold free_env_equiv; intros.
  apply eq_trans with (y := e2 x); auto.
Qed.

Lemma free_env_equiv_extend:
  forall E env1 env2 x t,
    free_env_equiv E env1 env2 ->
    free_env_equiv E (extend env1 x t) (extend env2 x t).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; auto.
Qed.

Lemma free_env_equiv_overwrite:
  forall E env x t1 t2,
    free_env_equiv E (extend (extend env x t1) x t2)
                     (extend env x t2).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; auto.
Qed.

Lemma free_env_equiv_neq:
  forall E env1 env2 x1 t1 x2 t2,
    x1 <> x2 ->
    free_env_equiv E env1 env2 ->
    free_env_equiv E (extend (extend env1 x1 t1) x2 t2)
                     (extend (extend env2 x2 t2) x1 t1).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; break_match; subst; auto.
  congruence.
Qed.

(* Here's where we prove interchangeability *)
Lemma free_env_equiv_typed:
  forall env1 ht e t,
    typed env1 ht e t ->
    forall env2,
      free_env_equiv e env1 env2 ->
      typed env2 ht e t.
Proof.
  unfold free_env_equiv.
  induction 1; intros.
  - constructor.
  - constructor.
  - constructor. symmetry.
    rewrite <- H. apply H0.
    constructor.
  - econstructor; eauto.
    + apply IHtyped1; intuition.
      apply H1; apply FreeApp_l; auto.
    + apply IHtyped2; intuition.
      apply H1; apply FreeApp_r; auto.
  - econstructor; eauto.
    apply IHtyped; auto.
    unfold extend; intros.
    break_match; auto.
    apply H0. constructor; auto.
  - constructor. auto.
  - constructor. apply IHtyped.
    intros.
    apply H0. constructor. auto.
  - constructor. apply IHtyped.
    intros.
    apply H0. constructor. auto.
  - econstructor.
    + apply IHtyped1. intros.
      apply H1. constructor. auto.
    + apply IHtyped2. intros.
      apply H1. apply FreeAssign_r. auto.
Qed.

(* OK, here's the lemma we needed all that for. The hard part of
proving preservation for the STLC is proving that substitution does
the right thing: if it substitutes something in for a variable in a
body, the body had better have the same type as if we just assumed
that x had that type. *)

(*

[PROBLEM 7 (10 points)]:

  Prove that substitution preserves typing.

*)
Lemma subst_pres_typed:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    closed e2 ->
    forall env ht tA tB,
      typed (extend env x tA) ht e1 tB ->
      typed env ht e2 tA ->
      typed env ht e3 tB.
Proof.
  
  (* About 52 tactics *)
Admitted.
(* END PROBLEM 7 *)

(** We're almost there. The last thing we'll need to do is to provide
a way to extend heap types with new values during our preservation
proof. To see why, let's take a look at a version of preservation that
looks a lot like the one for STLC without references: *)

Lemma wrong_preservation:
  forall h h' e e',
    h; e ==> h'; e' ->
    closed e ->
    forall ht t,
      heap_typed ht h ->
      typed E0 ht e t ->
      typed E0 ht e' t.
Abort.

(* The problem is that we're stuck with the same heap type. This is an
issue because when we allocate a new reference, we'll need to extend
our heap type with a type for the new reference cell. So let's
establish what it means for one heap to extend another: *)

Inductive heap_typ_extends: heap_typ -> heap_typ -> Prop :=
| heap_typ_extends_nil :
    forall h, heap_typ_extends h nil
| heap_typ_extends_cons :
    forall h h' x,
      heap_typ_extends h' h ->
      heap_typ_extends (x :: h') (x :: h).

(* We'll need some facts about this definition of heap extension. *)

(* If an address was in our heap type and we extend the heap, we don't
   affect the type for that address.
*)

(*

[PROBLEM 8 (5 points)]:

  Prove extends_lookup.

*)
Lemma extends_lookup :
  forall h h' a,
    a < length h ->
    heap_typ_extends h' h ->
    lookup_typ h' a = lookup_typ h a.
Proof.
  (* About 16 tactics *)
Admitted.
(* END PROBLEM 8 *)

(* Extending a heap increases its length *)
Lemma length_extends :
  forall h h',
    heap_typ_extends h' h ->
    forall a,
      a < length h ->
      a < length h'.
Proof.
  induction 1; intros; simpl in *.
  - omega.
  - destruct a.
    + omega.
    + apply lt_n_S. intuition.
Qed.

(* If we snoc a value onto a heap, that extends the heap. *)
Lemma extends_snoc :
  forall h x,
    heap_typ_extends (snoc h x) h.
Proof.
  intros.
  induction h; simpl in *;
  constructor; auto.
Qed.

(* Heaps extend themselves *)
Lemma extends_refl :
  forall h,
    heap_typ_extends h h.
Proof.
  induction h; constructor; auto.
Qed.

(* We'll need anonther version of weakening:
   types are preserved when extending heaps.
*)
Lemma heap_weakening :
  forall env ht ht' e t,
    typed env ht e t ->
    heap_typ_extends ht' ht ->
    typed env ht' e t.
Proof.
  induction 1; intros; simpl; try solve [econstructor; eauto].
  erewrite <- extends_lookup; eauto.
  constructor.
  eapply length_extends; eauto.
Qed.

(*

OK, we're ready to prove preservation. Note our new theorem
statement: Instead of saying that the term we step to is well-typed
with our starting heap type, we're now saying that there is *some*
heap type which is an extension of our heap type under which the new
term is well-typed. In practice, this new heap type will always either
be the same or the same plus a single type (when a new ref cell is
allocated). You'll need to be careful about when to provide a witness
for this existential, and "eexists" is your friend.

*)

(*

[PROBLEM 9 (30 points)]:

  Prove preservation.

*)
Lemma preservation:
  forall h h' e e',
    h; e ==> h'; e' ->
    closed e ->
    forall ht t,
      heap_typed ht h ->
      typed E0 ht e t ->
      exists ht',
        heap_typ_extends ht' ht /\
        typed E0 ht' e' t /\
        heap_typed ht' h'.
Proof.
  (* About 153 tactics *)
  induction 1; intros.
Admitted.
(* END PROBLEM 9 *)

(* Having proved progress and preservation,
   we're finally ready to prove soundness.
*)

(* Define the empty heap and the empty heap type *)
Definition H0 : heap := nil.
Definition HT0 : heap_typ := nil.

(* The empty heap is well-typed in the empty heap type. *)
Lemma empty_heap_typed :
  heap_typed HT0 H0.
Proof.
  split; simpl; auto.
  intros. omega.
Qed.

(* If a term is well-typed in an environment,
   then that environment better have definitions
   for all of that term's free variables. *)
Lemma typed_free_env:
  forall env ht e t,
    typed env ht e t ->
    forall x,
      free e x ->
      exists tx, env x = Some tx.
Proof.
  induction 1; intros.
  - inv H.
  - inv H.
  - inv H1; eauto.
  - inv H2.
    + apply IHtyped1; auto.
    + apply IHtyped2; auto.
  - inv H1. apply IHtyped in H4.
    destruct H4 as [tx Htx].
    exists tx. unfold extend in Htx.
    break_match; congruence.
  - inv H1.
  - inv H1. auto.
  - inv H1. auto.
  - inv H2; auto.
Qed.

(** Therefore, typing in empty env
    implies term is closed. *)
Lemma typed_E0_closed:
  forall ht e t,
    typed E0 ht e t ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply typed_free_env in H1; eauto.
  destruct H1. discriminate.
Qed.

(* OK, soundness time! *)

(* [PROBLEM 10 (15 points)]: Complete the proof of soundness. *)

(* First, prove that no term which is well-typed in an arbitrary heap
   can get stuck. This proof should use progress and preservation. *)

Lemma soundness' :
  forall h e t h' e',
    (h; e ==>* h'; e') ->
    forall ht,
      typed E0 ht e t ->
      heap_typed ht h ->
      (exists e'' h'', h'; e' ==> h''; e'') \/ isValue e'.
Proof.
  (* About 12 tactics *)
Admitted.

(* Now, prove that terms which are well-typed
   in the empty heap don't get stuck. *)
Lemma soundness :
  forall e t h' e',
    typed E0 HT0 e t ->
    (H0; e ==>* h'; e') ->
    (exists e'' h'', h'; e' ==> h''; e'') \/ isValue e'.
Proof.
  (* About 4 tactics *)
Admitted.
(* END PROBLEM 10 *)
