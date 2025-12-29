use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;
use std.booleans.print;
use std.str.print;

let main() = {
    let n = number_parse(list_get(args(), 1));

    let s = Struct!<number> {
        field: n * 2,
    };

    s.field = s.field + 1;

    print(s.field);

    s = Struct {
        field: 0,
    };

    print(s.field);

    s.field = 1;

    print(s.field);

    n = s.field;

    print(n);

    let s1 = Struct {
        field: true,
    };
    print(s1.field);

    let s1 = Struct {
        field: "Hello",
    };
    print(s1.field);

    print(Struct {
      field: 1,
    }.field);

    print(Struct {
      field: true,
    }.field);

    print(Struct {
      field: Struct {
        field: Struct {
          field: true
        }
      },
    }.field.field.field);

    # fixme:
    #print(Struct {
    #  field: "World",
    #}.field);
}

struct Struct<T> {
    field: T,
}
