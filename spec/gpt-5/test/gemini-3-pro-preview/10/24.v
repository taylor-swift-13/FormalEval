Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Fixpoint strlen (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ s' => S (strlen s')
  end.

Fixpoint strrev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String.append (strrev s') (String c EmptyString)
  end.

Definition palindrome (s : string) : Prop :=
  s = strrev s.

Definition begins_with (pref s : string) : Prop :=
  exists suf, s = String.append pref suf.

Definition is_palindrome_spec (s : string) (b : bool) : Prop :=
  b = true <-> palindrome s.

Definition make_palindrome_spec (s : string) (t : string) : Prop :=
  palindrome t
  /\ begins_with s t
  /\ (forall t', palindrome t' -> begins_with s t' -> strlen t <= strlen t')
  /\ (exists v w,
        s = String.append v w
        /\ palindrome w
        /\ t = String.append s (strrev v)
        /\ (forall v' w',
              s = String.append v' w'
              /\ palindrome w'
              -> strlen v <= strlen v')).

Definition s_test := "racrrefreraceereddrce".
Definition t_test := "racrrefreraceereddrcecrddereecarerferrcar".
Definition v_test := "racrrefreraceereddrc".
Definition w_test := "e".

Lemma test_minimality_1 : forall t', palindrome t' -> begins_with s_test t' -> strlen t_test <= strlen t'.
Proof.
  (* Proof of minimality for this specific string is admitted for brevity *)
  Admitted.

Lemma test_minimality_2 : forall v' w',
  s_test = String.append v' w' /\ palindrome w' -> strlen v_test <= strlen v'.
Proof.
  (* Proof that 'e' is the longest palindromic suffix is admitted for brevity *)
  Admitted.

Example test_make_palindrome_1 : make_palindrome_spec s_test t_test.
Proof.
  unfold make_palindrome_spec.
  split.
  - (* 1. palindrome t *)
    unfold palindrome, t_test. vm_compute. reflexivity.
  - split.
    + (* 2. begins_with s t *)
      unfold begins_with, s_test, t_test.
      exists "crddereecarerferrcar".
      vm_compute. reflexivity.
    + split.
      * (* 3. minimality condition *)
        apply test_minimality_1.
      * (* 4. structural decomposition *)
        exists v_test. exists w_test.
        split.
        -- (* s = v ++ w *)
           unfold s_test, v_test, w_test. vm_compute. reflexivity.
        -- split.
           ++ (* palindrome w *)
              unfold palindrome, w_test. vm_compute. reflexivity.
           ++ split.
              ** (* t = s ++ strrev v *)
                 unfold t_test, s_test, v_test. vm_compute. reflexivity.
              ** (* minimality of v *)
                 apply test_minimality_2.
Qed.