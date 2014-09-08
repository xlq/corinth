let rec comma_concat connective strings =
    match strings with
        | [] -> ""
        | [a] -> a
        | [a;b] -> a ^ " " ^ connective ^ " " ^ b
        | a::tail -> a ^ ", " ^ comma_concat connective tail
