Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => if is_uppercase c then nat_of_ascii c + sum_uppercase_ascii s'
              else sum_uppercase_ascii s'
  end.

Definition digitSum_impl (s : string) : nat := sum_uppercase_ascii s.

Definition problem_66_pre (s : string) : Prop := True.

Definition problem_66_spec (s : string) (output : nat) : Prop :=
  output = digitSum_impl s.

Example Example_test : problem_66_spec 
  (append "VtabsBCDEFGHIJKLMNOPQRSTUVThis" 
    (String (ascii_of_nat 10) 
      (append "is" 
        (String (ascii_of_nat 9) 
          (append "a" 
            (String (ascii_of_nat 9) 
              (append "test" 
                (String (ascii_of_nat 9) 
                  (append "with" 
                    (String (ascii_of_nat 10) 
                      (append "newlines" 
                        (String (ascii_of_nat 9) 
                          (append "and" 
                            (String (ascii_of_nat 9) "absWXYAThisZ")))))))))))))) 
  2269.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  vm_compute.
  reflexivity.
Qed.