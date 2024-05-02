// Tags: main, malloc, pointers, stdio
/** Description: 

    In this Rust example, a struct named NumberCollection contains a
    list of integers and a reference to one of these integers as the
    favorite. Lifetimes are used to ensure that the reference to the
    favorite number is valid for as long as the struct exists. This
    prevents dangling references by making sure that the reference
    does not outlive the data it points to, thereby maintaining memory
    safety.
    
*/

/* Rust code:
   
struct NumberCollection<'a> {
    numbers: Vec<i32>,
    favorite: &'a i32,
}

impl<'a> NumberCollection<'a> {
    // Constructs a new NumberCollection with a reference to a favorite number
    fn new(numbers: Vec<i32>, favorite_index: usize) -> NumberCollection<'a> {
        let favorite = &numbers[favorite_index]; // Borrowing a reference from the vector
        NumberCollection { numbers, favorite }
    }

    // Returns a reference to the favorite number
    fn get_favorite(&self) -> &'a i32 {
        self.favorite
    }
}

fn main() {
    let numbers = vec![10, 20, 30, 40, 50]; // A collection of numbers
    let collection = NumberCollection::new(numbers, 2); // '30' is the favorite

    println!("Favorite number: {}", collection.get_favorite());
    // The output will be: Favorite number: 30
}

*/

/* C + CN translation */

#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int* numbers;         // Pointer to a dynamically allocated array of integers
    int* favorite;        // Pointer to the favorite integer within the numbers array
    int size;             // To keep track of the size of the array
} NumberCollection;

// Function to create a NumberCollection
NumberCollection* create_number_collection(int* array, int size, int favorite_index) {
    NumberCollection* collection = malloc(sizeof(NumberCollection));
    if (collection == NULL) {
        fprintf(stderr, "Failed to allocate memory for NumberCollection\n");
        exit(EXIT_FAILURE);
    }
    
    // Allocate memory for the numbers array
    collection->numbers = malloc(size * sizeof(int));
    if (collection->numbers == NULL) {
        fprintf(stderr, "Failed to allocate memory for numbers\n");
        free(collection); // Clean up previously allocated memory
        exit(EXIT_FAILURE);
    }

    // Copy data from the given array to the newly allocated array
    for (int i = 0; i < size; i++) {
        collection->numbers[i] = array[i];
    }

    collection->size = size;
    collection->favorite = &collection->numbers[favorite_index]; // Set favorite

    return collection;
}

// Function to free NumberCollection
void free_number_collection(NumberCollection* collection) {
    free(collection->numbers); // First free the internal array
    free(collection); // Then free the struct itself
}

int main() {
    int numbers[] = {10, 20, 30, 40, 50};
    int size = sizeof(numbers) / sizeof(numbers[0]);
    NumberCollection* collection = create_number_collection(numbers, size, 2); // '30' is the favorite

    printf("Favorite number: %d\n", *collection->favorite);
    
    free_number_collection(collection);

    return 0;
}

