CREATE TABLE runs (
  -- The run id used in tests table
  id             integer    primary key autoincrement     not null,

  -- timestamp is supported in python if you do the following:
  --   conn = sqlite3.connect("flit.sqlite",
  --                          detect_types=sqlite3.PARSE_DECLTYPES)
  -- The secret sauce is in the "detect_types" that allows python to intercept
  -- it and convert it to a sqlite3 basic type and back.
  rdate          timestamp,

  -- The message describing what this run is all about
  label          text
  );
CREATE TABLE sqlite_sequence(name,seq);
CREATE TABLE tests (
  id             integer    primary key autoincrement     not null,
  run            integer,   -- run index from runs table
  name           varchar,   -- name of the test case
  host           varchar,   -- name of computer that ran the test
  compiler       varchar,   -- compiler name
  optl           varchar,   -- optimization level (e.g. "-O2")
  switches       varchar,   -- compiler flag(s) (e.g. "-ffast-math")
  precision      varchar,   -- precision (f = float, d = double, e = extended)
  comparison_hex varchar,   -- metric of comparison - hex value
  comparison     real,      -- metric of comparison of result vs ground truth
  file           varchar,   -- filename of test executable
  nanosec        integer    check(nanosec >= 0),  -- timing for the function

  foreign key(run) references runs(id)
  );
