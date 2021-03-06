from __future__ import annotations
from abc import abstractmethod
from typing import TypeVar, List, Generic, Any

T = TypeVar("T")


class Cons_1(Generic[T]):
    @abstractmethod
    def Allocate(self, len: int) -> List[T]:
        ...


def Helpers_allocateArrayFromCons(cons: Cons_1[T], len_1: int) -> List[T]:
    if cons is None:
        return (list)([None] * len_1)

    else:
        return cons([0] * len_1)


def Helpers_fillImpl(array: List[T], value: T, start: int, count: int) -> List[T]:
    for i in range(0, (count - 1) + 1, 1):
        array[i + start] = value
    return array


def Helpers_spliceImpl(array: List[T], start: int, delete_count: int) -> List[T]:
    for _ in range(1, delete_count + 1, 1):
        array.pop(start)
    return array


def Helpers_indexOfImpl(array: List[T], item: T, start: int) -> Any:
    try:
        return array.index(item, start)

    except Exception as ex:
        return -1
