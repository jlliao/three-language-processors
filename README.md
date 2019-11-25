# three-language-processors

The project consists of an interpreter for arithmetic expressions, a compiler from arithmetic expressions to byte code, and an interpreter for byte code (i.e., a virtual machine). 

The program is first implemented and tested in OCaml. Then the program is formalized in Coq Proof Assistant to computationally prove that for any given arithmetic expression, interpreting it will yield the same result as compiling the expression into a byte-code program and then running it.

Magritte interpreter does not directly operate on natural numbers, but synthetic expressions natural numbers.
