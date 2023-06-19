> erl -sname server
> c(server).
> server:init().

> erl -sname client
> c(client).
> client:start().
> client:send("This is a test!").
