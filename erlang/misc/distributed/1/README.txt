> erl -sname server
> c(server).

> erl -sname client
> c(client).
> client:start().
> client:send("This is a test!").
