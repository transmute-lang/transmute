use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;
use std.booleans.print;
use std.str.print;

let main() = {
    let n = number_parse(list_get(args(), 1));

    let s_number = Struct!<number> {
        field: n * 2,
    };
    s_number.field = s_number.field + 1;
    print(s_number.field);

    s_number = Struct {
        field: n * 2,
    };
    s_number.field = s_number.field + 1;
    print(s_number.field);

    n = s_number.field;
    print(n);

    let s_boolean = Struct {
        field: true,
    };
    print(s_boolean.field);

    let s_string = Struct {
        field: "Hello",
    };
    print(s_string.field);

    print(Struct {
      field: 1,
    }.field);

    print(Struct {
      field: true,
    }.field);

    print(Struct {
      field: "World",
    }.field);

    print(Struct {
      field: Struct {
        field: Struct {
          field: 1
        }
      },
    }.field.field.field);

    print(Struct {
      field: Struct {
        field: Struct {
          field: true
        }
      },
    }.field.field.field);

    print(Struct {
      field: Struct {
        field: Struct {
          field: "Hello, world"
        }
      },
    }.field.field.field);

    print(OtherStruct {
      field: Struct {
        field: "OK"
      }
    }.field.field);
}

struct Struct<T> {
    field: T,
}

struct OtherStruct<T> {
    field: T,
}
