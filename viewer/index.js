var database;

$(document).ready(function() {
    database = new Database($('#container'));
    var qc = new QueryCanvas($('#container'), database.outputRv);
    qc.heatmap(Predicate.conflicted,
               function(tc) { return tc.runid; });
    qc.heatbar(Predicate.conflicted);

    qc.table(
        // Enable the following when using separate details databases
        // function(tc) {
        //     // Lazy load detail databases
        //     if (!database.loadMscan('data/' + tc.runid + '-details.json'))
        //         return $('<span>').text('Loading details...');
        // }
    );

    // Load main mscan databases
    database.loadMscan('data/sv6.json');
    database.loadMscan('data/Linux.json');
});
