## Message Passing in Distributed Erlang

**Note:** all the nodes are running on the **same** machine,
it's "locally" distributed.

There are 3 ways for a `Client` process running on node `client@localhost` to send
a message to a `Server` process running on node `server@localhost`:

### 1. `Client` knows the PID of `Server`

The `Client` process may have spawned the `Server` process
on `server@localhost` or requested its PID.

*client.erl*

```erlang
ServerPid ! Msg
```

### 2. `Server` is locally registered

The `Server` process is registered **locally** as `server` on `server@localhost`.

*server.erl*

```erlang
register(server, ServerPid)
```

*client.erl*

```erlang
{server, server@localhost} ! Msg
```

### 3. `Server` is globally registered

The `Server` process is registered **globally** as `server` on `server@localhost`.

`global` functions work only after the two nodes are connected,
the standard way to do it is by using `net_adm:ping(Node)`.

If the `Client` spawns the `Server` there's no need to explicitly connect them.

*server.erl*

```erlang
global:register_name(server, ServerPid),
```

*client.erl*

```erlang
net_adm:ping(server@localhost). % Very important!
global:send(server, Msg)

% Alternative way
global:whereis_name(server) ! Msg
```
