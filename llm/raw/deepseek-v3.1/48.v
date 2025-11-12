
Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = (text = rev text).
