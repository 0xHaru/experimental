> erl -sname server
> c(server).
> server:init().

> erl -sname client
> c(client).
> nodes().
> client:start().
> nodes().
> client:send("This is a test!").
