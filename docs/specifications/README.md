# Specifications

CN specifications (specs) are a way of writing down what your code *should* do,
along with a set of tools for automatically testing and verifying that your
code does, in fact, do that.

## Special comments

CN specs are written in special `/*@ ... @*/` comments in C files.

```c
/*@ CN specs go here. @*/
/*@
    Or here, in multiline form.  Just like C multiline comments.
@*/
```

## Kinds of specs

CN specs can be added in several places.

<div class="grid cards" markdown>
-   **Function specifications**

    ---
    
    *Function specifications* are placed between function declarations and bodies.
    They contain requirements for successfully calling the function, as well as
    conditions the function ensures are true on exit.
    
    ```cn
    int my_function()
    /*@
        Function specification goes here.
    *@/
    {
        return 0;
    }
    ```
    
    [:octicons-arrow-right-24: Function specifications](function-specifications.md)
</div>

<div class="grid cards" markdown>
-   **Loop invariants**
    
    --- 
    
    *Loop invariants* are placed between a loop header and its body.  They specify
    conditions that are true prior to, during, and after the loop executes.

    ```cn
    int my_function()
    {
        for (int i = 0; i < 10; i++)
        /*@
            Loop invariant goes here.
        @*/
        {
            // ...
        }

        return 0;
    }
    ```
    
    [:octicons-arrow-right-24: Loop invariants](loop-invariants.md)
</div>

<div class="grid cards" markdown>
-   **Auxiliary definitions**
    
    ---
    
    CN lets you write auxiliary definitions to factor out common logic for
    reuse in more than one spec.  Auxiliary definitions are places at the top
    level of C files.
    
    ```cn
    /*@
        Auxiliary definitions go here.
    @*/

    // My function.
    int my_function()
    {
        return 0;
    }
    ```
    
    Auxiliary definitions can also be used to define simple data structures and
    algorithms that capture and verify the functional correctness of complex
    bits of code. This is an advanced feature.
    
    [:octicons-arrow-right-24: Auxiliary definitions](auxiliary-definitions/README.md)

</div>
