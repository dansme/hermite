AttachSpec("Hermite.spec");

SetVerbose("Quaternion", 1);
time res := FindHermiteOrders();
SetVerbose("Quaternion", 0);
orders := OrdersAsList(res);
orders_c := [ O : O in orders | HasCancellation(O) ];
SaveOrders("my_hermite.dat", orders);
SaveOrders("my_cancellation.dat", orders_c);
