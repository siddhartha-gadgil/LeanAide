def sieve_of_eratosthenes(n):
  # Define a list of integers from 2 to n
  numbers = list(range(2, n+1))

  # Define a list of boolean values to mark each number as either prime or composite
  is_prime = [True] * (n+1)

  # Define a list of prime numbers
  prime_numbers = []

  # Iterate over the list of numbers
  for i in range(2, n+ 1):
    # If the value of is_prime[i] is False, skip the inner for loop
    if is_prime[i]: 
        # Iterate over the list of numbers
        for j in range(2, (n //i) + 1):
        # set the value of is_prime[i * j] to False
           is_prime[i * j] = False
        # append i to the list of prime numbers
        prime_numbers.append(i)

  # Return the list of prime numbers
  return prime_numbers

# Test the sieve_of_eratosthenes function
print(sieve_of_eratosthenes(10)) # [2, 3, 5, 7]
print(sieve_of_eratosthenes(100)) # [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
print(sieve_of_eratosthenes(1000000))