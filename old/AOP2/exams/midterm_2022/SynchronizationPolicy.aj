privileged public aspect SynchronizationPolicy {
    pointcut matchGoCalls(CrossRoad cr)
        : call(public void CrossRoad.go()) && target(cr);

    after(CrossRoad cr) returning : matchGoCalls(cr) {
        TrafficLight[] tls = cr.tls;
        boolean flag = true;

        for (int prev = 0, i = 1; i < tls.length; prev += 1, i += 1) {
            if(!tls[prev].state.equals(cr.tls[i].state)) {
                flag = false;
                break;
            }
        }

        if (flag) {
            if(tls.length % 2 == 0) {
                for (int i = 0; i < tls.length; i += 2)
                    tls[i].state = Colors.next(tls[i].state);
            } else {
                for (int i = 1; i < tls.length; i += 2)
                    tls[i].state = Colors.next(tls[i].state);
            }
        }
    }
}

// WRONG RESULTS
