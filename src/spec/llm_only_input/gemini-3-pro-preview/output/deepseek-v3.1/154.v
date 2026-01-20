Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Bool.
Require Import Arith.
Require Import Lia.

Open Scope string_scope.
Open Scope nat_scope.

(* Implementations for the parameters to allow concrete evaluation *)
Definition string_append := String.append.
Definition string_length := String.length.
Definition string_eq := String.eqb.

(* Helper function to check if 's' starts with 'prefix' *)
Fixpoint starts_with (prefix s : string) : bool :=
  match prefix with
  | EmptyString => true
  | String c1 prefix' => 
      match s with
      | EmptyString => false
      | String c2 s' => if Ascii.eqb c1 c2 then starts_with prefix' s' else false
      end
  end.

(* Implementation of string_in (substring check) *)
Fixpoint string_in (sub s : string) : bool :=
  match s with
  | EmptyString => starts_with sub s
  | String _ s' => if starts_with sub s then true else string_in sub s'
  end.

(* The Specification *)
Definition cycpattern_check_spec (a : string) (b : string) (result : bool) : Prop :=
  (string_eq a b = true -> result = true) /\
  (string_eq b "" = true -> result = true) /\
  (forall (i : nat), (i < string_length b)%nat -> 
    string_in (string_append (substring i (string_length b - i) b) 
                            (substring 0 i b)) a = true -> result = true) /\
  ((string_eq a b = false) -> 
   (string_eq b "" = false) -> 
   (forall (i : nat), (i < string_length b)%nat -> 
    string_in (string_append (substring i (string_length b - i) b) 
                            (substring 0 i b)) a = false) -> result = false).

(* The Test Case Proof *)
Example test_case_xyzw_xyw : cycpattern_check_spec "xyzw" "xyw" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  - (* Case 1: string_eq a b = true -> result = true *)
    intro H.
    (* "xyzw" is not equal to "xyw", so H implies False *)
    simpl in H. discriminate H.
  - split.
    + (* Case 2: string_eq b "" = true -> result = true *)
      intro H.
      (* "xyw" is not empty, so H implies False *)
      simpl in H. discriminate H.
    + split.
      * (* Case 3: Cyclic permutations check *)
        intros i Hi Hin.
        (* The length of "xyw" is 3. We analyze i = 0, 1, 2 *)
        simpl in Hi.
        (* Break down i to check specific cases *)
        destruct i.
        { (* i = 0 *) simpl in Hin. discriminate Hin. }
        destruct i.
        { (* i = 1 *) simpl in Hin. discriminate Hin. }
        destruct i.
        { (* i = 2 *) simpl in Hin. discriminate Hin. }
        (* For i >= 3, it contradicts Hi *)
        lia.
      * (* Case 4: Negative conditions -> result = false *)
        intros Hneq Hnotempty Hforall.
        (* The result is already false, so this holds trivially *)
        reflexivity.
Qed.