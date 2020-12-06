#define N_OF_TRAFFIC_LIGHTS 4
#define N_OF_INTERSECTIONS 3
#define CAR 1

/* traffic light's naming */
#define NE 0
#define EW 1
#define ES 2
#define SW 3

/* options to reduce intersection operations */
#define lock_intersection(int_id, tl_id) \
    lock[int_id] ! LOCK(tl_id); \
    accept[tl_id] ? ACCEPT
#define unlock_intersection(int_id) \
    release[int_id] ! RELEASE

/* messages used to communicate between intersections and traffic lights */
mtype = { LOCK, ACCEPT, RELEASE }
mtype = { RED, GREEN }
mtype traffic_lights_color[N_OF_TRAFFIC_LIGHTS]

chan lock[N_OF_INTERSECTIONS] = [N_OF_TRAFFIC_LIGHTS] of { mtype, byte }
chan accept[N_OF_TRAFFIC_LIGHTS] = [0] of { mtype }
chan release[N_OF_INTERSECTIONS] = [0] of { mtype }
chan car_sensor[N_OF_TRAFFIC_LIGHTS] = [1] of { bit }

proctype road_traffic_generator(byte init_tl_id) {
    byte tl_id;

    tl_id = init_tl_id;
    do
    :: car_sensor[tl_id] ! CAR;
    od
}

proctype intersection(byte init_int_id) {
    byte int_id, tl_id;

    int_id = init_int_id;    
    do
    :: lock[int_id] ? LOCK(tl_id) -> 
        accept[tl_id] ! ACCEPT;
        release[int_id] ? RELEASE;
    od
}

proctype traffic_light_controller(byte init_tl_id) {
    byte tl_id;
    tl_id = init_tl_id;

    do
    :: car_sensor[tl_id] ? [CAR] ->
        /* obtain resources (intersections) */
        if
        :: tl_id == NE ->
            lock_intersection(0, tl_id);
            lock_intersection(1, tl_id);
        :: tl_id == EW ->
            lock_intersection(0, tl_id);
        :: tl_id == ES ->
            lock_intersection(1, tl_id);
            lock_intersection(2, tl_id);
        :: tl_id == SW ->
            lock_intersection(2, tl_id);
        fi;

        /* process road traffic */
        atomic {
            traffic_lights_color[tl_id] = GREEN;
            printf("MSC: Traffix light #%d: GREEN\n", tl_id);
            car_sensor[tl_id] ? CAR;
        }
        atomic {
            traffic_lights_color[tl_id] = RED;
            printf("MSC: Traffic light #%d: RED\n", tl_id);
        }

        /* release resources (intersections) */
        if
        :: tl_id == NE ->
            unlock_intersection(1);
            unlock_intersection(0);
        :: tl_id == EW ->
            unlock_intersection(0);
        :: tl_id == ES ->
            unlock_intersection(2);
            unlock_intersection(1);
        :: tl_id == SW ->
            unlock_intersection(2);
        fi
    od
}

init {
    byte int_id, tl_id;

    /* Reset traffic lights colors */
    tl_id = 0;
    do
    :: tl_id < N_OF_TRAFFIC_LIGHTS ->
        traffic_lights_color[tl_id] = RED;
        tl_id++;
    :: else -> break;
    od;
    
    atomic
    {
        /* Start intersection managers processes */
        int_id = 0;
        do
        :: int_id < N_OF_INTERSECTIONS ->
            run intersection(int_id);
            int_id++;
        :: else -> break;
        od;
    
        /* Start traffic lights processes */
        tl_id = 0;
        do
        :: tl_id < N_OF_TRAFFIC_LIGHTS ->
            run traffic_light_controller(tl_id);
            tl_id++;
        :: else -> break;
        od;
    
        /* Start cars generator process */
        tl_id = 0;
        do
        :: tl_id < N_OF_TRAFFIC_LIGHTS ->
            run road_traffic_generator(tl_id);
            tl_id++;
        :: else -> break;
        od;
    }
}
