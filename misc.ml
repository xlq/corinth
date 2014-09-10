let rec comma_concat connective strings =
    match strings with
        | [] -> ""
        | [a] -> a
        | [a;b] -> a ^ " " ^ connective ^ " " ^ b
        | a::tail -> a ^ ", " ^ comma_concat connective tail

let unsome = function
    | Some x -> x
    | None -> raise (Failure "unsome")

let rec times n s =
    match n with
        | 0 -> ""
        | n -> s ^ times (n-1) s
