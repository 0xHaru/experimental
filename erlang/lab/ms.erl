-module(ms).
-export([start/1, to_slave/2, status/0]).

start(NumSlaves) ->
    MasterPid = spawn(fun() -> master(NumSlaves) end),
    register(master, MasterPid),
    io:format("~p - Spawned the master process: ~p | [CLIENT]~n", [self(), MasterPid]).

to_slave(SlaveId, Msg) ->
    master ! {self(), relay, SlaveId, Msg},
    receive
        ok -> ok
    end.

status() ->
    master ! {self(), status},
    receive
        ok -> ok
    end.

spawn_slaves(N) -> spawn_slaves(N, []).

spawn_slaves(0, SlavePids) -> lists:reverse(SlavePids);
spawn_slaves(N, SlavePids) ->
    Pid = spawn(fun() -> slave_loop() end),
    spawn_slaves(N - 1, [Pid | SlavePids]).

slave_loop() ->
    receive
        die -> exit("received die message");
        Msg ->
            io:format("~p - Echoing this message: ~p | [SLAVE]~n", [self(), Msg]),
            slave_loop()
    end.

master(NumSlaves) ->
    process_flag(trap_exit, true),
    SlavePids = spawn_slaves(NumSlaves),
    lists:foreach(fun(Pid) -> link(Pid) end, SlavePids),
    io:format("~p - Spawned the slave processes: ~p | [MASTER]~n", [self(), SlavePids]),
    master_loop(SlavePids).

master_loop(SlavePids) ->
    receive
        {'EXIT', SlavePid, Reason} ->
            NewSlavePid = spawn(fun() -> slave_loop() end),
            io:format("~p - Process ~p died, reason: ~p | [MASTER]~n",
                      [self(), SlavePid, Reason]),
            io:format("~p - Restarting process ~p with new PID ~p | [MASTER]~n",
                      [self(), SlavePid, NewSlavePid]),
            UpdatedSlavePids = update_slaves(SlavePids, SlavePid, NewSlavePid),
            master_loop(UpdatedSlavePids);
        {ClientPid, status} ->
            io:format("~p - Slaves: ~p | [MASTER]~n", [self(), SlavePids]),
            ClientPid ! ok,
            master_loop(SlavePids);
        {ClientPid, relay, SlaveId, Msg} ->
            SlavePid = lists:nth(SlaveId, SlavePids),
            io:format("~p - Relaying ~p to slave ~p | [MASTER]~n", [self(), Msg, SlavePid]),
            SlavePid ! Msg,
            ClientPid ! ok,
            master_loop(SlavePids);
        Any ->
            io:format("~p - Invalid message: ~p | [MASTER]~n", [self(), Any]),
            master_loop(SlavePids)
    end.

update_slaves([SlavePid | T], SlavePid, NewSlavePid) -> [NewSlavePid | T];
update_slaves([H | T], SlavePid, NewSlavePid) ->
    [H | update_slaves(T, SlavePid, NewSlavePid)].

% erl
% c(ms).
% ms:start(2).
% ms:status().
% ms:to_slave(1, "This is a test!").
% ms:to_slave(2, "This is another test!").
% ms:to_slave(1, die).
% ms:status().
% ms:to_slave(1, "This is a new test!").
