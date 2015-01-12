**kuc** is a vector programming language with closures.

##### Compiling

Run `make` to build. Edit the Makefile to configure.

##### Examples

Lexical closures and garbage collection:

    kuc> {a:!x;.{a+1}} 5                    # closures
    kuc> {b:a:!x;.{a+:1;b::|b};(a;b)} 5     # closures!
    kuc> o:.{a:0;`add`show!{a+:x},{show a}} # objects
    kuc> (o`add) 5; (o`add) 7; .o`show

Simple JIT:

    kuc> ackermann:{$[x;self[x-1;$[y;self[x;y-1];1]];y+1]}
    kuc> time {ackermann[3;9]}
    kuc> disasm ackermann # tail-call-to-self optimization
    kuc> time {-1+|/(#{@[x;!*|x;|:]}\)'1+!-7} # fannkuch

More new language features:

    kuc> {[x]{[y]y-x}}[3;5] # curried functions
    kuc> _17%5     # compound operators (cf (_:)17%5)
    kuc> ~^108810b # null bool
    kuc> write[`:/dev/stdout]"Hello, world!\n";

Also see the [test programs](test).
