
We create this variation of `Class2Relational`, called `Class2Relational_tactic_test`. In particular, the original `Class2Table` rule splits into `Class2Table1` and `Class2Table2`, based on the name of source `Class`. In other words, there are more than one rule that creates the same output pattern.

```
module Class2Relational_tactic_test; 
create OUT : RelationalMetamodel from IN : ClassMetamodel;

rule Class2Table1 {
    from 
        c : Class (c.name = "Person")
    to 
        tab: Table (
        id <- c.id,
        name <- c.name,
        columns <- c.attributes->collect(a | thisModule.resolve([a, c], 'col'))
        )
}
rule Class2Table2 {
    from 
        c : Class (c.name != "Person")
    to 
        tab: Table (
        id <- c.id,
        name <- c.name,
        columns <- c.attributes->collect(a | thisModule.resolve([a, c], 'col'))
        )
}
rule Attribute2Column {
    from 
        a : Attribute,
        c : Class
        (not a.derived and a.type = c)
    to 
        col: Column (
        id <- a.id,
        name <- a.name,
        reference <- thisModule.resolve(c, 'tab')
        )
}
```