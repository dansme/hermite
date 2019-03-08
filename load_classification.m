AttachSpec("Hermite.spec");

// This loads the results from an already finished classification
orders_plus := LoadOrdersPlus("hermite.dat");
orders_c_plus := LoadOrdersPlus("cancellation.dat");
orders := [ O[1] : O in orders_plus ];
orders_c := [ O[1] : O in orders_c_plus ];
